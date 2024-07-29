import std/os/path
import std/os/file
import newstd/data/sort
import compiler/syntax/lexeme
import compiler/syntax/syntax
import compiler/syntax/promote
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/parse

fun test()
  parseProgramFromFile(True, "compiler/syntax/parse.kk".path)

fun parseProgramFromFile(fname: path, semiInsert: bool = True)
  val r = read-text-file(fname)
  parseProgramFromString(r, fname, semiInsert)

fun parseProgramFromString(input: string, fname: path, semiInsert: bool = True)
  lexParse(semiInsert, fn(x) x, parseProgram, fname.string, input)

fun interactive(f: () -> <ast> a): <ast> a
  val x = f()
  pmany("semicolons", pSemicolon)
  x

fun parseProgram()
  pmany("semicolons", pSemicolon)
  val p = pModule()
  peof()
  p

fun pModule()
  val res = optionMaybe("module name")
    val vis = pVisibility().fst
    val doc = pDocKeyword("module").snd
    val (name, rng) = pModulePath() 
    pBody(vis, name, rng, doc)
  match res
    Just(r) -> r
    Nothing -> pBody(Public, sourceInfo.name.path.basename.pathToModuleName, null, "")

fun pBody(vis: visibility, name: name, rng: range, doc: string): <ast> userProgram
  pmany("semicolons", pSemicolon)
  val (imports, fixDefss, topDefss) = braced
    val imps = semis("imports", pImportDecl)
    val fixs = semis("fixities", pFixityDecl)
    val tdefs = semis("topDefs", fn() pTopDef(vis))
    (imps, fixs, tdefs)
  pmany("semicolons", pSemicolon)
  val (defs, typeDefs, externals) = splitTopDefs(topDefss.concat)
  val prelude = if name.show.starts-with("std/core").is-just then [] else [Kimport(nameSystemCore, nameSystemCore, null, Private)]
  Program(sourceInfo, name, rng, [TypeDefRec(typeDefs)], [DefRec(defs)], prelude ++ imports, externals, fixDefss.concat, doc)

value type topDef
  DefValue(def: userDef)
  DefType(def: userTypeDef)
  DefExtern(def: external)

// TODO: Compiler doesn't optimize common case of sequential matching of same constructor
fun splitTopDefs(dfs: list<topDef>): (list<userDef>, list<userTypeDef>, list<external>)
  fun split(dfs': list<topDef>, userDefs: ctx<list<userDef>>, typeDefs: ctx<list<userTypeDef>>, externDefs: ctx<list<external>>): (list<userDef>, list<userTypeDef>, list<external>)
    match dfs'
      Cons(DefValue(d), rst) -> rst.split(userDefs ++ ctx Cons(d, _), typeDefs, externDefs)
      Cons(DefType(d), rst) -> rst.split(userDefs, typeDefs ++ ctx Cons(d, _), externDefs)
      Cons(DefExtern(d), rst) -> rst.split(userDefs, typeDefs, externDefs ++ ctx Cons(d, _))
      Nil -> (userDefs ++. Nil, typeDefs ++. Nil, externDefs ++. Nil)
  dfs.split(ctx _, ctx _, ctx _)

fun pTopDef(vis): <ast> list<topDef>
  choices("topDef", [
    {[DefValue(pPureDecl(vis))]},
    {[DefType(pAliasDecl(vis))]},
    {
      val (tdef, cdefs) = pTypeDecl(vis)
      Cons(DefType(tdef), cdefs.map(DefValue))
    },
    {pEffectDecl(vis)},
    {pExternDecl(vis)}
  ])

fun pImportDecl(): <ast> kimport
  val (vis, vrng) = pVisibility(Private)
  pKeyword("import")
  val (asname, name, rng) = pImportAlias()
  Kimport(asname, name, combine(vrng, rng), vis)

fun pVisibility(vis=Private)
  choicesnb("visibility", [{
    val rng = pKeyword("pub", ["public"])
    (Public, rng)
  },
  {
    val rng = pKeyword("private")
    addWarning("using private is deprecated, only use pub to make declarations public", rng)
    (Private, rng)
  },{(vis, null)}])

fun typeFromPars(rng:range, pars: list<valueBinder<userType, maybe<userExpr>>>, teff: userType, tres: userType): div userType
  promoteType(TpFun(pars.map(fn(p) (p.name, p.binderType)), teff, tres, rng))

fun genArgs(pars: list<valueBinder<userType, maybe<userExpr>>>): list<(maybe<(name, range)>, userExpr)>
  pars.map(fn(p) (Nothing, Var(p.name, False, p.range.before)))

fun genParArgs(tp: userType)
  match tp
    TpQuan(QSome) -> astError("external types cannot contain unspecified ('_') types", tp.range)
    TpQuan(QExists) -> astError("external types cannot contain existential types", tp.range)
    TpQuan(_, _, t) -> t.genParArgs
    TpQual(_, t) -> t.genParArgs
    TpParens(t) -> t.genParArgs
    TpAnn(t, _) -> t.genParArgs
    TpFun(pars) -> pars.genFunParArgs
    _ -> astError("external declarations must have a function type", tp.range)

fun genFunParArgs(pars: list<(name, userType)>)
  pars.map-indexed(fn(i, p) p.genParArg(i)).unzip 

fun genParArg((name:name, _:userType), idx: int)
  val fullName = if name == nil then new-hidden-name("arg" ++ idx.show) else name
  (ValueBinder(fullName, Nothing, Nothing, null, null), (Nothing, Var(fullName, False, null)))

fun pExternDecl(dvis: visibility): <ast> list<topDef>
  choicesnb("externDecl", [{
    val krng = pDocKeyword("extern").fst
    val _ = choicesnb("import", [
      {pKeyword("import"); ()},
      {
        pSpecialId("include"); 
        warnDeprecated("include", "import", krng); 
      }])
    [DefExtern(pExternalImport(krng))]
  }, {
    val (vis,vrng) = pVisibility(dvis)
    val inl = pInline()
    val fip = pFip()
    val (krng,doc) = pDocKeyword("extern",[])
    val (name, nameRng) = pFunId()
    val (pars, pinfos, args, tp, annotate) = choicesnb("extern type", [
      {
        pKeyword(":")
        val tp = pType()
        val (pars, args) = genParArgs(promoteType(tp))
        (pars, [], args, tp, fn(body) Ann(body, tp, tp.range))
      },
      {
        val tpPars = pTypeParams()
        val (pars, pinfos, _) = pDeclParams(True, !inl.is-inlineAlways)
        val (teff, tres) = pAnnotResult()
        val tp = typeFromPars(nameRng, pars, teff, tres)
        (pars.map(fn(ValueBinder(name', tp', expr, rng1, rng2)) ValueBinder(name', Just(tp'), expr, rng1, rng2)), pinfos, genArgs(pars), tp, fn(body) promote([], tpPars, [], Just((Just(teff), tres)), body))
      }
    ])
    val (exprs, rng) = pExternalBody()
    val fullRng = combine([krng, vrng, rng])
    if (inl.is-inlineAlways) then [DefExtern(External(name, tp, pinfos, nameRng, fullRng, exprs, vis, fip, doc))]
    else
      val externName = newHiddenExternalName(name)
      val ext = External(externName, tp, pinfos, nameRng.before, fullRng.before, exprs, Private, fip, doc)
      val body = annotate(Lam(pars, App(Var(externName, False, null), args, fullRng), fullRng))
      val binder = ValueBinder(name, (), body, nameRng, fullRng)
      val extfun = Def(binder, fullRng, vis, def-fun-ex(pinfos, fip), InlineNever, doc)
      [DefExtern(ext), DefValue(extfun)]
  }
  ])

fun pExternalImportKeyVal()
  val key = pExternalImportKey()
  pKeyword("=")
  val (v, _) = pStringLit()
  (key, v)

fun pExternalImportKey()
  val (id, _) = pVarId()
  id.show

fun externalIncludes(target: target, rng: range, (key, fname): (string, string))
  val currentFile = rng.source.name
  val fpath = currentFile.path.dirname / fname
  if target.is-c && fpath.extname == "" && key == "file" then
    [("header-include-inline", preadFile(fpath.change-ext("h"))), ("include-inline", preadFile(fpath.change-ext("c")))]
  elif target.is-c && key == "header-file" then
    [("header-include-inline", preadFile(fpath))]
  elif target.is-c && key == "header-end-file" then
    [("header-end-include-inline", preadFile(fpath))]
  elif key == "file" then
    [("include-inline", preadFile(fpath))]
  else [(key, fpath.show)]

fun preadFile(fpath: path)
  catch({read-text-file(fpath)}, fn(e) astError("Unable to read external file at path: " ++ fpath.show ++ ": got error " ++ e.message, null))

fun pExternalImportEntry() 
  val target = pExternalTarget()
  val (keyvals, rng) = choicesnb("", [
    {val key = pExternalImportKey(); val (v, rng) = pStringLit(); ([(key, v)], rng)},
    {semiBraces("", pExternalImportKeyVal)}
    ])
  (target, keyvals.map(fn(kv) externalIncludes(target, rng, kv)).concat)

fun pExternalImport(r: range): <ast> external
  choicesnb("import", [
    {
      pKeyword("=")
      val entry = pExternalImportEntry()
      ExternalImport([entry], r)
    },{
      val (entries, rng2) = semiBraces("entries", pExternalImportEntry)
      ExternalImport(entries, r.combine(rng2))
    }
  ])
 
fun pExternalBody()
  semiBraces("external entries", pExternalEntry)

fun pExternalEntry()
  val (target, inl, _) = pExternalEntryRanged()
  (target, inl)

fun pExternalEntryRanged()
  val target = pExternalTarget()
  val (call, rng) = pExternalCall()
  (target, call, rng)

fun pExternalCall()
  val f = optionMaybe("specialId", {pSpecialId("inline"); ExternalInline}).default(ExternalCall)
  val (s, rng) = pStringLit()
  (f(s), rng)

fun pExternalTarget()
  choicesnb("target", [
    {pSpecialId("c"); C(CDefault)},
    {pSpecialId("cs"); CS},
    {pSpecialId("js"); JS(JsDefault)},
    {DefaultTarget}
  ])

fun pFixityDecl(): <ast> list<fixDef>
  val (vis, vrng, assoc) = try("", {val (vis, vrng) = pVisibility(Private); val assoc = pAssocDef(); (vis, vrng, assoc)})
  val (prec, lex) = pInteger()
  if prec < 0 || prec > 100 then
    astError("fixity must be between 0 and 100", lex.range)
  val names = pSepBy1("names", pIdentifier, pComma)
  names.map(fn((name, rng)) FixDef(name, FixInfix(prec, assoc), rng.combine(vrng), vis))

fun pAssocDef()
  choicesnb("associativity", [
    {pKeyword("infixl"); AssocLeft},
    {pKeyword("infixr"); AssocRight},
    {pKeyword("infix"); AssocNone}
  ])

fun pAliasDecl(dvis: visibility)
  val (vis, vrng, trng, doc) = try("")
    val (vis, vrng) = pVisibility(dvis)
    val (trng, doc) = pDocKeyword("alias")
    (vis, vrng, trng, doc)
  val tbind = pTBinderDef()
  val (tpars, kind, krng) = pTypeKindParams()
  pKeyword("=")
  val tp = pType()
  val range = combine([vrng, trng, krng, tp.range])
  Synonym(tbind(kind), tpars, tp, range, vis, doc) 

fun pTypeDecl(vis: visibility)
  choicesnb("type", [{pDataTypeDecl(vis)}, {pStructDecl(vis)}])

fun pDataTypeDecl(dvis: visibility)
  val (vis, defvis, vrng, (typeSort, trng, doc, ddef, isExtend)) = choicesnb("type", [
    {
      val rng = pKeyword("abstract")
      val x = pTypeDeclKind()
      (Public, Private, rng, x)
    },
    {
      val (vis, rng) = pVisibility(dvis)
      val x = pTypeDeclKind()
      (vis, vis, rng, x)
    }
  ])
  val tbind =
    if isExtend then
      val (qid, rng) = pQTypeId()
      fn(kind) TypeBinder(qid, kind, rng, rng)
    else pTBinderDef()
  val (tpars, k, prng) = pTypeKindParams()
  val name = tbind(k)
  val resTp = TpApp(name.tpCon, tpars.map(tpVar), name.range.combine(tpars.last.map(range).default(name.range)))
  val (cs, crng) = maybe("", {semiBraces("", {pConstructor(defvis, tpars, resTp)})}).default(([], null))
  val (constrs, creatorss) = cs.unzip
  val range = combine([vrng, trng, name.range, prng, crng])
  (DataType(name, tpars, constrs, range, vis, typeSort, ddef, isExtend, doc), creatorss.concat)

fun pStructDecl(dvis': visibility)
  val ((vis, defvis, ddef), (vrng, trng, doc)) = try("", {
    val (vis, defvis, rng) = choicesnb("", [
      {val rng = pKeyword("abstract"); (Public, Private, rng)},
      {val (vis, rng) = pVisibility(dvis'); (vis, vis, rng)}
    ])
    val ddef = choicesnb("", [
      {pSpecialId("value"); DataDefValue(valueReprZero)},
      {pSpecialId("ref", ["reference"]); DataDefNormal},
      {DataDefAuto}
    ])
    val (trng, doc) = pDocKeyword("struct")
    ((vis, defvis, ddef), (rng, trng, doc))
  })
  val tbind = pTBinderDef()
  val tpars = maybe("", {angles(pTBinders).fst}).default([])
  val n = tbind(KindNone)
  val resTp = TpApp(n.tpCon, tpars.map(tpVar), n.range.combine(tpars.last.map(range).default(n.range)))
  val (pars, prng) = pConPars(defvis)
  val (tid, rng) = (n.name, n.name-range)
  val conId = tid.toConstructorName
  val (usercon, creators) = makeUserCon(conId, tpars, resTp, [], pars, rng, rng.combine(prng), defvis, doc)
  (DataType(n, tpars, [usercon], combine([vrng, trng, rng, prng]), vis, Inductive, ddef, False, doc), creators)

fun tpVar(tb: typeBinder<k>)
  TpVar(tb.name, tb.range)

fun tpCon(tb: typeBinder<k>)
  TpCon(tb.name, tb.range)

fun pTypeDeclKind()
  choices("", [
    {
      val (rng1, kind) = choicesnb("", 
        [{val rng = pSpecialId("rec"); (rng, Retractive)},
         {val rng = pSpecialId("co"); (rng, CoInductive)}])
      val (rng2, doc) = pDocKeyword("type")
      (kind, rng1.combine(rng2), doc, DataDefNormal, False)
    },
    {
      val (ddef, isExtend) = choicesnb("", [
        {pSpecialId("open"); (DataDefOpen, False)},
        {pSpecialId("extend"); (DataDefOpen, True)},
        {pSpecialId("value"); (DataDefValue(valueReprZero), False)},
        {pSpecialId("ref", ["reference"]); (DataDefNormal, False)},
        {(DataDefAuto, False)}
      ])
      val (rng, doc) = pDocKeyword("type")
      (Inductive, rng, doc, ddef, isExtend)
    }
  ])

fun pTypeKindParams()
  choicesnb("", [
    {val (tpars, rng) = angles(pTBinders); val kind = pKindAnnot(); (tpars, kind, rng.combine(kind.range))},
    {val kind = pKindAnnot(); ([], kind, kind.range)},
    {([], KindNone, null)}
  ])

fun pConstructor(dvis: visibility, foralls: list<userTypeBinder>, resTp: userType)
  val (vis, vrng) = pVisibility(dvis)
  val (rng0, doc) = optionMaybe("", {pDocKeyword("con")}).default((null, ""))
  val (constr, rng) = pConstructorId()
  val exists0 = pTypeParams()
  val (pars, prng) = pConPars(vis)
  makeUserCon(constr, foralls, resTp, exists0, pars, rng, combine([vrng, rng0, rng, prng]), vis, doc)

fun makeUserCon(const: name, foralls: list<userTypeBinder>, resTp: userType, exists0: list<userTypeBinder>, pars: list<(visibility, valueBinder<userType, maybe<userExpr>>)>, nameRng: range, rng: range, vis: visibility, doc: string)
  val conParams = pars.map(fn((v, p)) (v, p(expr=Nothing)))
  val cName = const.new-creator-name
  val params = pars.map(fn((_, p)) p(binderType=if p.expr.is-just then makeOptional(p.binderType) else p.binderType))
  val lParams = params.map(fn(ValueBinder(name', _, expr, nameRng', rng')) ValueBinder(name', Nothing, expr, nameRng', rng') )
  val arguments = params.map(fn(p) (Nothing, Var(p.name, False, p.name-range)))
  val tpParams = params.map(fn(p) (p.name, p.binderType))
  val tpFull = quantify(QForall, foralls, TpFun(tpParams, makeTpTotal(nameRng), resTp, rng))
  val body = Ann(Lam(lParams, App(Var(const, False, nameRng), arguments, rng), rng), tpFull, rng)
  val binder = ValueBinder(cName, (), body, nameRng, nameRng)
  val creator = Def(binder, rng, vis, DefFun([]), InlineAlways, doc) 
  (UserCon(const, exists0, conParams, Nothing, nameRng, rng, vis, doc), if pars.any(fn(p) p.snd.expr.is-just) then [creator] else [])

fun pConPars(dvis: visibility)
  choicesnb("", [{semiBraces("", {pConBinder(dvis)})}, {parensCommas({pConBinder(dvis)})}, {([], null)}])

fun pConBinder(dvis: visibility)
  val (vis, vrng) = pVisibility(dvis)
  val (name, rng, tp) = pParamType()
  val (opt, drng) = pDefaultExpr()
  (vis, ValueBinder(name, tp, opt, rng, vrng.combine(rng).combine(tp.range).combine(drng)))

alias param = (visibility, valueBinder<userType, maybe<userExpr>>);

fun bindExprToVal(opname: name, oprange: range, expr: userExpr)
  val fresh = "value".make-fresh-hidden-name(opname, oprange)
  val freshVar = Var(fresh, False, oprange)
  val erange = expr.range
  val binder = Def(ValueBinder(fresh, (), expr, oprange, erange), oprange, Private, DefVal, InlineAuto, "")
  (fn(b) Bind(binder, b, erange), fn(params) freshVar)

struct opDecl
  opdoc: string
  name: name
  kwdrng: range
  idrng: range
  lin: bool // linear
  sort: operationSort
  exists0: list<typeBinder<userKind>>
  pars: list<valueBinder<userType, maybe<userExpr>>>
  prng: range
  mbteff: maybe<userType>
  tres: userType;

struct effectDecl
  vis: visibility
  vis2: visibility
  r1: range
  r2: range
  name: string
  kind: dataKind
  lin: bool
  inst: bool
  scoped: bool
  n: name
  r3: range
  exists0: list<typeBinder<userKind>>
  k: userKind
  r4: range
  umbrella: maybe<list<userType>>
  decls: list<opDecl>;

struct funDef
  tpars: list<typeBinder<userKind>> 
  pars: list<valueBinder<maybe<userType>, maybe<userExpr>>>
  pinfos: list<paramInfo>
  parsRng: range
  mbTres: maybe<(maybe<userType>, userType)>
  preds: list<userType>
  ann: (userExpr -> <ast> userExpr);

fun pEffectDecl(dvis: visibility)
  val (vis, defVis, vrng) = choices("", [{val (v, vr) = pVisibility(dvis); (v, v, vr)}, {val vr = pKeyword("abstract"); (Public, Private, vr)}])
  val isInstance = optionMaybe("named", {pKeyword("named")}).is-just
  val isScoped = optionMaybe("scoped", {pKeyword("scoped")}).is-just
  val (rng1, singleShot) = optionMaybe("linear", {val rng = pKeyword("linear"); (rng, True)}).default((null, False))
  val sort = optionMaybe("sort", {pSpecialId("rec"); Retractive}).default(Inductive)
  val (rng2, doc) = pDocKeyword("effect")
  val erng = rng1.combine(rng2)
  makeEffectDecl(choices("", [{
    val (effectId, irng) = pTypeId()
    val (tpars, kind, prng) = pTypeKindParams()
    val mbInstanceUmb = if !isInstance then Nothing else 
      Just(choices("", [
        {pKeyword("in"); [pType(), TpCon(nameTpPartial, irng)]}, 
        {if isScoped then [] else [TpCon(nameTpPartial, irng)]}]))
    val (operations, _) = semiBraces("", {pOpDecl(singleShot, defVis)})
    EffectDecl(vis, defVis, vrng, erng, doc, sort, singleShot, isInstance, isScoped, effectId, irng, tpars, kind, prng, mbInstanceUmb, operations)
   },
   {
    val (tpars, kind, _) = pTypeKindParams()
    val op = pOpDecl(singleShot, vis)
    val mbInstance = Nothing
    val opId = op.name
    val effectId = if opId.isValueOperationName then opId.fromValueOperationsName else opId
    EffectDecl(vis, defVis, vrng, erng, op.opdoc, sort, singleShot || op.lin, False, isScoped, effectId, op.idrng.extend(-1), tpars, kind, op.prng, mbInstance, [op])
   }
  ]))

fun pDocKeywordEffect()
  pDocKeyword("effect", ["context", "ambient"])

fun pKeywordFun()
  pKeyword("fun")

fun pDocKeywordFun()
  pDocKeyword("fun",[])

fun pKeywordInject()
  pKeyword("mask", ["inject"])

fun makeEffectDecl(decl: effectDecl): pure list<topDef>
  val EffectDecl(vis, _, vrng, erng, doc, sort, singleShot, isInstance, isScoped, id, irng, tpars, effkind, _, mbInstanceUmb, operations) = decl
  val rng = vrng.combine(erng).combine(irng)
  val (tparsScoped, tparsNonScoped) = if isScoped then (tpars.take(1), tpars.drop(1)) else ([], tpars)
  val infKind = match effkind
    KindNone -> tpars.map(kind).foldr(KindCon(if isInstance then nameKindStar elif singleShot then nameKindHandled1 else nameKindHandled, null)) fn(e, acc)
      KindArrow(e, acc)
    _ -> effkind
  val ename = TypeBinder(id, infKind, irng, irng)
  val effTpH = TpApp(TpCon(ename.name, ename.range), tpars.map(tpVar), null)
  val effTp = if isInstance then effTpH else TpApp(TpCon(if singleShot then nameTpHandled1 else nameTpHandled, ename.range), [effTpH], null)
  // declare the effect type (for resources, generate a hidden constructor to check the types)
  val docEffect = "`:" ++ id.show ++ "` effect"
  val docx = if doc != "" then doc else "// " ++ docEffect
  // Effect handler type
  val hndName = id.to-handler-name
  val kindStar = KindCon(nameKindStar, null)
  val kidnEffect = KindCon(nameKindEffect, null)
  val hndTpName = TypeBinder(hndName, KindNone, null, null)
  val hndEffTp = TypeBinder("e".new-hidden-name, KindCon(nameKindEffect, null), null, null)
  val hndResTp = TypeBinder("r".new-hidden-name, kindStar, null, null)
  val hndTp = TpApp(hndTpName.tpCon, (tparsNonScoped ++ [hndEffTp, hndResTp]).map(tpVar), null)

  val (effTpDecl, wrapAction) = 
    if isInstance then 
      val evTp = TpApp(TpCon(nameTpEv, rng), [TpApp(hndTpName.tpCon, tparsNonScoped.map(tpVar), rng)], rng)
      val evName = "ev".new-name
      val evFld = ValueBinder(evName, evTp, Nothing, irng, rng)
      val evCon = UserCon(id.to-constructor-name, [], [(Private, evFld)], Nothing, irng, rng, Private, "")
      (DataType(ename, tpars, [evCon], rng, vis, Inductive, DataDefNormal, False, docx), 
        fn(action) Lam([ValueBinder(evName, Nothing, Nothing, irng, rng)], 
          App(action, [(Nothing, 
            App(Var(id.to-constructor-name, False, rng), [(Nothing, Var(evName, False, rng))], rng))], rng), rng))
    else
      // add a private constructor that refers to the handler type to get a proper recursion check
      val hndfld = ValueBinder(nil, hndTp, Nothing, irng, irng)
      val hndcon = UserCon(id.to-constructor-name, [hndEffTp, hndResTp], [(Private, hndfld)], Nothing, irng, irng, Private, "")
      (DataType(ename, tpars, [hndcon], rng, vis, Inductive, DataDefNormal, False, docx), fn(action) action)
  
  // Effect tag
  val tagName = id.to-effect-tag-name
  val tagDef = Def(ValueBinder(tagName, (), Ann(App(Var(nameHTag, False, null), 
    [(Nothing, Literal(LitString(id.show ++ "." ++ irng.source.name.path.basename, null)))], null), 
      quantify(QForall, tpars, TpApp(TpCon(nameTpHTag, null), 
        [TpApp(TpCon(hndName, null), tparsNonScoped.map(tpVar), null)], null)), null),
       null, null), null, vis, DefVal, InlineNever, "// runtime tag for the " ++ docEffect)
  val scopeEff = TpApp(TpCon(nameTpScope, null), tparsScoped.map(fn(tb) TpVar(tb.name, null)), null)
  val extraEffects = (if isScoped && isInstance then [scopeEff] else []) ++ (if sort.is-retractive then [TpCon(nameTpDiv, null)] else [])
  

  // parse the operations and return the constructor fields and function definitions
  val orderedOperations = operations.sort-by(fn(op1:opDecl, op2:opDecl) (op1.name).name/name/cmp(op2.name))
  val opCount = operations.length
  val (opFields, opSelects, opDefs, opValDefs) = list(0, opCount - 1).zip(orderedOperations).map(fn(op) operationDecl(opCount, vis, tparsScoped, tparsNonScoped, docEffect, hndName, id, mbInstanceUmb, effTp, hndTpName.tpCon, ([hndEffTp, hndResTp]), extraEffects, op)).unzip4
  
  // Handle function
  val hndCon = UserCon(hndName.to-constructor-name, [], opFields.map(fn(f) (Public, f)), Nothing, null, null, vis, "")
  val hndTpDecl = DataType(hndTpName, tparsNonScoped ++ [hndEffTp, hndResTp], [hndCon], null, vis, sort, DataDefNormal, False, "// handler for the " ++ docEffect)
  val handleRetTp = TypeBinder("b".new-hidden-name, kindStar, null, null)
  val handleName = id.to-handle-name
  val handleEff = 
    if isInstance then 
      if isScoped then makeEffectExtend(scopeEff, hndEffTp.tpVar) 
      else hndEffTp.tpVar 
    else makeEffectExtend(effTp, hndEffTp.tpVar)
  val actionArgTp = if isInstance then [("hname".new-name, effTp)] else []
  val actionTp = TpFun(actionArgTp, handleEff, handleRetTp.tpVar, null)
  val handleTp = quantify(QForall, tparsNonScoped ++ [handleRetTp, hndEffTp, hndResTp], TpFun(
    [("cfc".new-name, TpCon(nameTpInt32, null)),
    ("hnd".new-name, TpApp(TpCon(hndName, null), (tparsNonScoped ++ [hndEffTp, hndResTp]).map(tpVar), null)),
    ("ret".new-name, TpFun([("res".new-name, handleRetTp.tpVar)], hndEffTp.tpVar, hndResTp.tpVar, null)),
    ("action".new-name, if isScoped then quantify(QForall, tparsScoped, actionTp) else actionTp)],
    hndEffTp.tpVar, hndResTp.tpVar, null
  ))
  val params = [
    ValueBinder("cfc".new-name, Nothing, Nothing, null, null),
    ValueBinder("hnd".new-name, Nothing, Nothing, null, null),
    ValueBinder("ret".new-name, Nothing, Nothing, null, null),
    ValueBinder("action".new-name, Nothing, Nothing, null, null)]
  val arguments = [
    (Nothing, Var(tagName, False, null)),
    (Nothing, Var("cfc".new-name, False, null)),
    (Nothing, Var("hnd".new-name, False, null)),
    (Nothing, Var("ret".new-name, False, null)),
    (Nothing, wrapAction(Var(new-name("action"), False, null)))
  ]
  val handleInner = App(Var(if isInstance then nameNamedHandle else nameHandle, False, null), arguments, null)
  val handleBody = Ann(Lam(params, handleInner, null), handleTp, null)
  val handleDef = Def(ValueBinder(handleName, (), handleBody, irng, rng), null, vis, DefFun([]), InlineNever, "// handler for the " ++ docEffect)
  [DefType(effTpDecl), DefValue(tagDef), DefType(hndTpDecl), DefValue(handleDef)] ++ opSelects.map(DefValue) ++ opDefs.map(DefValue) ++ opValDefs.concat-maybe.map(DefValue)

fun pOpDecl(lin: bool, vis: visibility)
  choicesnb("op decl", [
    {pValOpDecl(vis)},
    {pFunOpDecl(lin, vis)}
  ])

// effect NAME {val op = ...}
// TODO: annotate the operation as "value operation" to
// (a) also constrain the definition in the handler to use `val`
// (b) constrain the use site to use it as a value
fun pValOpDecl(vis: visibility): <ast> opDecl
  val (rng0, doc) = pDocKeyword("val")
  val (id, idrng) = pIdentifier()
  pKeyword(":")
  val (mbTeff, tRes) = pTResult()
  if mbTeff.is-just then
    astError("an explicit effect in result type of an operation is not allowed (yet)", mbTeff.map(fn(t) t.range).default(rng0))
  OpDecl(doc, id.to-value-operation-name, rng0, idrng, True, OpVal, [], [], idrng, mbTeff, tRes)

fun pFunOpDecl(lin: bool, vis: visibility): <ast> opDecl
  val ((rng0, doc), sort) = choicesnb("op decl", [
    {(pDocKeywordFun(), OpFun)},{
      val rdoc = pDocKeyword("ctl", ["control"])
      if lin then astError("'ctl' operations are invalide for a linear effect", rdoc.fst)
      else (rdoc, OpControl)
    },{
     val rdoc = pDocKeyword("final", ["except", "brk"]);
     pKeyword("ctl")
     if lin then astError("'final ctl' operations are invalide for a linear effect", rdoc.fst)
     else (rdoc, OpExcept)
    }
  ])
  val (id, idrng) = pIdentifier()
  val exists0 = pTypeParams()
  val (pars, _, prng) = pDeclParams(False, True)
  pKeyword(":")
  val (mbTeff, tRes) = pTResult()
  if mbTeff.is-just then
    astError("an explicit effect in result type of an operation is not allowed (yet)", mbTeff.map(fn(t) t.range).default(rng0))
  OpDecl(doc, id, rng0, idrng, False, sort, exists0, pars, prng, mbTeff, tRes)

fun pDeclParams(allowBorrow: bool, allowDefaults: bool)
  fun pParamBinder() 
    val pinfo = if allowBorrow then pParamInfo() else Own
    val (name, rng, tp) = pParamType()
    val (opt, drng) = if allowDefaults then pDefaultExpr() else (Nothing, null)
    (ValueBinder(name, tp, opt, rng, combine([rng, tp.range(range), drng])), pinfo)
  val (ipars, rng) = parensCommas(pParamBinder)
  val (pars, pinfos) = ipars.unzip
  (pars, pinfos, rng)

fun operationDecl(opCount, vis, forallsScoped:list<userTypeBinder>, forallsNonScoped, docEffect, hndName, effName, mbInstanceUmb:maybe<list<userType>>, effTp, hndTp, hndTpVars, extraEffects, (opIndex, op))
  val foralls = forallsScoped ++ forallsNonScoped
  val OpDecl(_doc, id, _kwrng, idrng, _lin, sort, exists0, pars, _prng, _mbTeff, tRes) = op
  val rng = idrng
  val opEffTps = mbInstanceUmb.default([effTp])
  val teff0 = (opEffTps ++ extraEffects).foldr(null.makeEffectEmpty, fn(e, acc) makeEffectExtend(e, acc))
  val nameA = ".a".new-name
  val tpVarA = TpVar(nameA, null)
  val isInstance = mbInstanceUmb.is-just
  val exists1 = if exists0.is-cons then exists0 else promoteFree(foralls, (pars.map(binderType) ++ [teff0, tRes]))
  fun notDiv(tp)
    match tp
      TpCon(name, _) -> !(name == nameTpDiv)
      _ -> True
  val teff = if (forallsNonScoped ++ exists1).is-cons && isInstance && extraEffects.all(notDiv) then makeEffectExtend(TpCon(nameTpDiv, null), teff0) else teff0
  // create a constructor field for the operation as `clauseId : clauseN<a1,..,aN,b,e,r>`
  val forallParams = forallsNonScoped.map(fn(par) TpVar(par.name, null))
  val tpParams = forallParams ++ exists1.map(fn(par) TpVar(par.name, null))
  fun makeClauseFieldName(opSort:operationSort, name)
    prepend(opSort.show ++ "-", if name.is-value-operation-name then name.from-value-operations-name else name)
  val clauseId = makeClauseFieldName(sort, id)
  val (clauseName, clauseParsTp) = if pars.length <= 2 then (name-tp-clause(pars.length), pars.map(binderType)) else (name-tp-clause(1), [TpApp(TpCon(name-tuple(pars.length), null), pars.map(binderType), null)])
  val clauseRhoTp = TpApp(TpCon(clauseName, null), clauseParsTp ++ Cons(tRes, Cons(TpApp(hndTp, forallsNonScoped.map(tpVar), null), hndTpVars.map(tpVar))), null)
  val clauseTp = quantify(QForall, exists1 ++ forallsScoped, clauseRhoTp)
  val conField = ValueBinder(clauseId, clauseTp, Nothing, null, null)
  val selectId = id.to-op-selector-name
  fun createSelect()
    val hndArg = "hnd".new-name
    val hndParam = ValueBinder(hndArg, Nothing, Nothing, null, null)
    val i = opIndex;
    val fieldCount = opCount
    val patterns = list(0, i - 1).map(fn(_) (Nothing, PatWild(null))) ++ 
      [(Nothing, PatVar(ValueBinder(clauseId, Nothing, PatWild(null), null, null)))] ++ 
      list(i+1, fieldCount - 1).map(fn(_) (Nothing, PatWild(null)))
    val branch = Branch(PatCon(hndName.to-constructor-name, patterns, null, null), [Guard(guardTrue, Var(clauseId, False, null))])
    val innerBody = Case(Var(hndArg, False, null), [branch], null)
    val fullTp = quantify(QForall, foralls ++ exists1 ++ hndTpVars, TpFun([(hndArg, TpApp(hndTp, (forallsNonScoped ++ hndTpVars).map(tpVar), null))], makeTpTotal(null), clauseRhoTp, null))
    val body = Ann(Lam([hndParam], innerBody, null), fullTp, null)
    val binder = ValueBinder(selectId, (), body, rng, rng)
    Def(binder, null, vis, DefFun([Borrow]), InlineAlways, ("// select `" ++ id.show ++ "` operation out of the " ++ docEffect ++ " handler"))
  // create an operation selector explicitly so we can hide the handler constructor
  val opSelect = createSelect()
  // create a typed perform wrapper: fun op(x1:a1,..,xN:aN) : <l> b { performN(evv-at(0),clause-op,x1,..,xN) }
  fun createOp()
    val nameRng = idrng
    val hasExists = exists1.is-cons
    val perform = Var(name-perform(pars.length), False, null)
    val zeroIdx = App(Var(nameSSizeT, False, null), [(Nothing, Literal(LitInt(0, null)))], null)
    val resourceName = "hname".new-hidden-name
    val resourceBinder = ValueBinder(resourceName, effTp, Nothing, null, null)
    val params0 = pars.map(fn(par) par(binderType=if par.expr.is-just then par.binderType.makeOptional else par.binderType))
    val params = if isInstance then Cons(resourceBinder, params0) else params0
    val arguments = params0.map(fn(par) (Nothing, Var(par.name, False, par.name-range)))
    val lParams = params.map(fn(ValueBinder(name, _, expr, nameRng', rng')) ValueBinder(name, Nothing, expr, nameRng', rng') )
    val tplParams = params.map(fn(par) (par.name, par.binderType))
    val tpFull = quantify(QForall, foralls ++ exists1, TpFun(tplParams, teff, tRes, null))
    val inner = 
      if isInstance then 
        Case(Var(resourceName, False, null), 
         [Branch(PatCon(effName.to-constructor-name, [(Nothing, PatVar(ValueBinder("ev".new-name, Nothing, PatWild(null), null, null)))], null, null), 
           [Guard(guardTrue, Var("ev".new-name, False, null))])], null)
      else App(Var(nameEvvAt, False, null), [(Nothing, zeroIdx)], null)
    val innerBody = App(perform, [(Nothing, inner), (Nothing, Var(selectId, False, null))] ++ arguments, null)
    val body = Ann(Lam(lParams, innerBody, rng), tpFull, rng)
    val binder = ValueBinder(id, (), body, nameRng, nameRng)
    Def(binder, idrng, vis, DefFun([]), InlineAlways, "// call `" ++ id.show ++ "` operation of the " ++ docEffect)
  val opDef = createOp()

  if id.is-value-operation-name then
    // create a temporary value definition for type checking
    val opName = id.from-value-operations-name
    val qualTpe = promoteType(TpApp(TpCon(nameTpValueOp, null), [tRes], null))
    val phantom = App(Var(nameValueOp, False, null), [], null)
    val annot = Ann(phantom, qualTpe, null)
    return (conField, opSelect, opDef, Just(Def(ValueBinder(opName, (), annot, idrng, null), null, vis, DefVal, InlineNever, "// phantom definition for value operations")))
  (conField, opSelect, opDef, Nothing)

fun pPureDecl(dvis: visibility)
  val (vis, vrng) = pVisibility(dvis)
  val inl = pInline()
  choicesnb("", [
    {val (rng, doc) = pDocKeyword("val"); pValDecl(vrng.combine(rng), doc, vis, inl)},
    {val f = pFip(); val (rng, doc) = pDocKeywordFun(); pFunDecl(vrng.combine(rng), doc, vis, inl, f)},
    {pKeyword("fn"); astError("hint: use 'fun' to start a named function definition (and 'fn' for anonymous functions)", peek().range)}
  ])

fun pFunctionDecl(vrng: range, vis: visibility)
  val inl = pInline()
  val f = pFip()
  val (rng, doc) = pDocKeywordFun()
  pFunDecl(vrng.combine(rng), doc, vis, inl, f)

fun pVarDecl()
  val (vrng, doc) = pDocKeyword("var")
  val bind = pBinder(vrng)
  pKeyword(":=")
  val body = pBlockExpr()
  Def(bind(body), vrng.combine(body.range), Private, DefVar, InlineNever, doc)

fun pValDecl(rng: range, doc: string, vis: visibility, inl: defInline)
  val bind = pBinder(rng)
  pKeyword("=")
  val body = pBlockExpr()
  Def(bind(body), rng.combine(body.range), vis, DefVal, inl, doc)

fun pFunDecl(rng: range, doc: string, vis: visibility, inl: defInline, f: fipT)
  val spars = sQuantifier()
  val (name, nameRng) = pFunId()
  val FunDef(tpars, pars, pinfos, _, mbTres, preds, ann) = pFunDef(True)
  val body = pBodyExpr()
  val fnct = promote(spars, tpars, preds, mbTres, Lam(pars, body, rng.combine(body.range)))
  Def(ValueBinder(name, (), ann(fnct), nameRng, nameRng), rng.combine(fnct.range), vis, def-fun-ex(pinfos, f), inl, doc)

fun pFunDef(allowBorrow: bool)
  val tpars = pTypeParams()
  val (pars, pinfos, transform, rng) = pParameters(allowBorrow, True)
  val resultTp = pAnnotRes()
  val preds = maybe("predicates", {pKeyword("with"); parens({pmany1("", pPredicate)}).fst}).default([])
  FunDef(tpars, pars, pinfos, rng, resultTp, preds, transform)

fun pAnnotRes()
  maybe("") fn()
    val (teff, tres) = pAnnotResult()
    (Just(teff), tres)

fun pAnnotResult()
  pKeyword(":")
  pTResultTotal()

fun pTypeParams()
  maybeList({angles(pTBinders).fst})

fun pParameters(allowBorrow: bool, allowDefaults: bool)
  val (results, rng) = parensCommas({pParameter(allowBorrow, allowDefaults)})
  val (binders, pinfos, transforms) = results.unzip3
  fun transform(e: userExpr): <ast> userExpr
    transforms.foldr(e, fn(f, e') f(e'))
  (binders, pinfos, transform, rng)

fun pParameter(allowBorrow: bool, allowDefaults: bool)
  val pinfo = if allowBorrow then pParamInfo() else Own
  val pat = pPatAtom()
  val tp = optionMaybe("", pTypeAnnotPar)
  val (opt, drng) = if allowDefaults then pDefaultExpr() else (Nothing, range/range/null)
  val rng = match pat
    PatVar(binder) -> binder.expr.range
    _ -> pat.range
  fun binder(name: name, nameRng: range)
    ValueBinder(name, tp, opt, nameRng, combine([rng, tp.map(fn(t) t.range).default(rng), drng]))
  match pat
    PatVar(ValueBinder(name, Nothing, PatWild, nameRng, _)) -> (binder(name, nameRng), pinfo, fn(x) x)
    PatWild(nameRng) -> (binder("_wildcard".uniqueRangeHiddenName(nameRng), nameRng), pinfo, fn(x) x)
    _ -> 
      val name = "pat".uniqueRangeHiddenName(rng)
      fun transform(e)
        match e
          Lam(binders, body, lambdaRng) -> Lam(binders, Case(Var(name, False, rng), [Branch(pat, [Guard(guardTrue, body)])], rng), lambdaRng)
          Ann(body, tp', rng') -> Ann(body.transform, tp', rng')
          _ -> astError("Syntax.Parse.parameter: unexpected function expression in parameter match transform", rng)
      (binder(name, rng), pinfo, transform)

fun makeOptional(tp: userType)
  TpApp(TpCon(nameTpOptional, tp.range), [tp], tp.range)

fun pDefaultExpr()
  optionMaybe("default", {val krng = pKeyword("="); val e = pExpr(); (Just(e), krng.combine(e.range))}).default((Nothing, null))

fun anyStatVar(l: list<statement>): maybe<userDef>
  match l
    Cons(StatVar(def'), _) -> Just(def')
    Cons(_, tl) -> tl.anyStatVar
    Nil -> Nothing

fun combine(e1: statement, e2: userExpr)
  match e1
    StatFun(f) -> f(e2)
    StatExpr(e) ->
      val r = e.range
      Bind(Def(ValueBinder("_".new-name, (), e, r, r), r, Private, DefVal, InlineAuto, ""), e2, r)
    StatVar(def') ->
      val ValueBinder(name, (), expr, nameRng, rng) = def'.binder
      App(Var(nameLocal, False, rng), 
       [(Nothing, expr), 
        (Nothing, Parens(Lam([ValueBinder(name, Nothing, Nothing, nameRng, nameRng)], e2, range/combine(def'.range,e2.range)), name, rng))],
       range/combine(rng, e2.range))

fun localScope(vdef: userDef, exp: userExpr): userExpr
  val erng = exp.range
  val drng = vdef.range
  val nrng = vdef.binder.name-range
  App(Var(nameRunLocal, False, nrng), [(Nothing, Lam([], exp, erng))], drng)

fun pBlock(): <ast> userExpr
  val rng1 = pLcurly()
  pmany("semicolons", pSemicolon)
  val stmts1 = semis("statements", pStatement)
  val stmts2 = optionMaybe("", {val rng2 = pKeyword("return"); val e = pExpr(); pmany("semicolons", pSemicolon); [StatExpr(makeReturn(rng2, e))]}).default([])
  val rng2 = pRcurly()
  val localize = match stmts1.anyStatVar { Just(def) -> [StatFun(fn(e) localScope(def, e))]; Nothing -> []}
  val stats = localize ++ stmts1 ++ stmts2
  match stats.reverse
    Cons(StatExpr(exp), rst) -> Parens(rst.foldr(exp, combine), nil, rng1.combine(rng2))
    [] -> Var(nameUnit, False, rng1.combine(rng2))
    _ -> astError("Last statement in a block must be an expression", rng1.combine(rng2))

fun makeReturn(r: range, e: userExpr)
  App(Var(nameReturn, False, r), [(Nothing, e)], r.combine(e.range))

value type statement
  StatFun(e: (userExpr -> <ast> userExpr))
  StatExpr(e: userExpr)
  StatVar(e: userDef)

fun pStatement()
  choicesnb("statement", [
   {
    val funs = pmany1("", {pFunctionDecl(null, Private)})
    StatFun(fn(body) Let(DefRec(funs), body, body.range.combine(funs.last.map(fn(f) f.range).default(body.range))))
   },
   {StatFun(pLocalValueDecl())},
   {StatVar(pVarDecl())},
   {
    val f = pWithStat()
    maybe("", {pKeyword("in"); StatExpr(f(pBlockExpr()))}).default(StatFun(f))
   },
   {StatExpr(choices("", [pBasicExpr, pReturnExpr]))} 
  ]) 

fun pLocalValueDecl(): <ast> (userExpr -> <ast> userExpr)
  val krng = pKeyword("val")
  val pat = pPattern()
  pKeyword("=")
  val e = pBlockExpr()
  fun bindVar(binder:valueBinder<maybe<userType>, pattern<userType>>, mbTyp: maybe<userType>, rng: range): <ast> (userExpr -> <ast> userExpr)
    val annExpr = match mbTyp
      Just(tp) -> Ann(e, tp.promoteType, rng)
      Nothing -> e
    val vBinder = ValueBinder(binder.name, (), annExpr, binder.name-range, binder.range)
    fn(b) Bind(Def(vBinder, rng, Private, DefVal, InlineAuto, ""), b, krng.combine(b.range))
  match pat.unParens
    PatVar(binder as ValueBinder(expr=PatWild)) -> bindVar(binder, binder.binderType, binder.range) 
    PatAnn(PatVar(binder as ValueBinder(expr=PatWild)), tp, rng) -> bindVar(binder, Just(tp), rng)
    _ -> fn(b) Case(e, [Branch(pat, [Guard(guardTrue, b)])], krng.combine(b.range))

fun pWithStat()
  fun promoteValueBinder(binder)
    match binder.binderType
      Just(tp) -> binder(binderType=Just(tp.promoteType))
      _ -> binder
  val krng = pKeyword("with")
  choices("", [
    {
      val (par, _, transform) = pParameter(False, False)
      pKeyword("=")
      pKeyword("<-")
      val e = choices("", [pBasicExpr, {pHandlerExprStat(krng, HandlerInstance)}])
      fn(b) applyToContinuation(krng, [par.promoteValueBinder], e.transform, b)
    },
    {
      val e = choices("", [pBasicExpr, {pHandlerExprStat(krng, HandlerNormal)}])
      fn(b) applyToContinuation(krng, [], e, b)
    }
  ])

fun expr/unParens(e: expr<t>): expr<t>
    match e
      Parens(p) -> p.unParens
      _ -> e

fun patt/unParens(e: pattern<t>): pattern<t>
    match e
      PatParens(p) -> p.unParens
      _ -> e

fun applyToContinuation(wrng: range, params: list<valueBinder<maybe<t>, maybe<expr<t>>>>, expr: expr<t>, body: expr<t>): <ast> expr<t>  
  val f = Lam(params, body, wrng.combine(body.range))
  val funarg = [(Nothing, f)]
  val fullrange = wrng.combine(f.range)
  match expr.unParens
    App(f', args, _) -> App(f', (args ++ funarg), fullrange)
    atom -> App(atom, funarg, fullrange)

fun pTypeAnnotation(): <ast> (userExpr -> <ast> userExpr)
  maybe("", {
    val tp = pTypeAnnot()
    fn(x) Ann(x, tp, tp.range.combine(x.range))
  }).default(fn(x) x)

fun pBodyExpr()
  choices("", [pBlockExpr, {pKeyword("->"); pBlockExpr()}])

fun pBlockExpr()
  choicesnb("expression", [pWithExpr, pBFunExpr, pReturnExpr, pValExpr, pBasicExpr])

fun pExpr()
  choicesnb("expression", [pWithExpr, pFunExpr, pReturnExpr, pValExpr, pBasicExpr])

fun pBasicExpr()
  choicesnb("basic expression", [pIfExpr, pFnExpr, pMatchExpr, pHandlerExpr, pOpExpr])

fun pWithExpr()
  val f = pWithStat()
  pKeyword("in")
  f(pBlockExpr())

fun pValExpr()
  val f = pLocalValueDecl()
  pKeyword("in")
  f(pExpr())

fun pBFunExpr()
  choices("", [pBlock, {pLambda(["fun"])}])

fun pFunExpr()
  choices("", [pFunBlock, {pLambda(["fun"])}])

inline fun pFnExpr()
  pLambda([])

fun pFunBlock()
  val exp = pBlock()
  Lam([], exp, exp.range)

fun pLambda(alts)
  val rng = pKeyword("fn", alts)
  val spars = sQuantifier()
  val FunDef(tpars, pars, _, _, mbTres, preds, ann) = pFunDef(False)
  val body = pBodyExpr()
  val f = promote(spars, tpars, preds, mbTres, Lam(pars, body, rng.combine(body.range)))
  ann(f)

fun pIfExpr()
  val rng = pKeyword("if")
  val tst = pNtlExpr()
  val (tExpr, eExprs, eExpr) =
    choices("",[
      {
        val tExpr = pReturnExpr()
        (tExpr, [], Var(nameUnit, False, tExpr.range.after))
      },
      {
        val tExpr = pThenExpr(rng)
        val eExprs = pmany("", pElif)
        val eExpr = optionMaybe("", {pKeyword("else"); pBlockExpr()}).default(Var(nameUnit, False, (tExpr.range).combine(eExprs.map(fn(e) e.snd.range).combine).after))
        (tExpr, eExprs, eExpr)
      }
    ])
  Cons((tst, tExpr), eExprs).foldr(eExpr) fn((tst', tExpr'), eExpr')
    Case(tst', [Branch(PatCon(nameTrue, [], null, null), [Guard(guardTrue, tExpr')]),
              Branch(PatCon(nameFalse, [], null, null), [Guard(guardTrue, eExpr')])], tst'.range.combine(eExpr'.range))
  
fun pElif(): <ast> (userExpr, userExpr)
  val rng = pKeyword("elif")
  val tst = pNtlExpr()
  val tExpr = pThenExpr(rng)
  (tst, tExpr)

fun pThenExpr(rng: range): <ast> userExpr
  choicesnb("then", [
    {pKeyword("then"); pBlockExpr()},
    {
      val expr = pBlockExpr()
      addWarning("warning " ++ expr.range.before.start.show ++ ": using an 'if' without 'then' is deprecated.\n hint: add the 'then' keyword.", expr.range) 
      expr
    }
  ])

fun pReturnExpr(): <ast> userExpr
  val rng = pKeyword("return")
  val exp = pExpr()
  makeReturn(rng, exp)

fun pMatchExpr()
  choices("", [{
    val rng = pKeyword("match")
    val tst = pNtlExpr()
    val (branches, rng2) = semiBraces("match clause", pBranch)
    Case(tst, branches, rng.combine(rng2))
  },pHandlerExpr])

fun pHandlerExpr()
  val (rng0, hsort) = optionMaybe("", {val rng = pKeyword("named"); (rng, HandlerInstance)}).default((null, HandlerNormal))
  choices("handle or handler", [
    {
      val rng1 = pKeyword("handle")
      val rng = rng0.combine(rng1)
      val scoped = optionMaybe("", {pSpecialId("scoped"); HandlerScoped}).default(HandlerNoScope)
      val (over, mbEff) = pHandlerOverride(hsort)
      val arg = pNtlExpr()
      val expr = pHandlerClauses(rng, mbEff, scoped, over, hsort)
      App(expr, [(Nothing, arg)], rng.combine(expr.range))
    },
    {
      val rng1 = pKeyword("handler")
      val rng = rng0.combine(rng1)
      pHandlerExprX(rng, hsort)
    }
  ])

fun pHandlerExprStat(rng: range, hSort: handlerSort)
  match hSort
    HandlerNormal -> pHandlerExprX(rng, hSort)
    HandlerInstance ->
      pKeyword("named")
      optionMaybe("", {pKeyword("handler")})
      pHandlerExprX(rng, hSort)

fun pHandlerExprX(rng: range, hSort: handlerSort)
  val scoped = maybe("", {pKeyword("scoped"); HandlerScoped}).default(HandlerNoScope)
  val (over, mbEff) = pHandlerOverride(hSort)
  pHandlerClauses(rng, mbEff, scoped, over, hSort)

fun pHandlerOverride(hSort: handlerSort)
  val over = match hSort
    HandlerNormal -> 
      maybe("", {pKeyword("override"); HandlerOverride}).default(HandlerNoOverride)
    _ -> HandlerNoOverride
  val mbEff = maybe("", {val eff = angles(pType).fst; eff.promoteType})
  (over, mbEff)

fun pHandlerClauses(rng: range, mbEff: maybe<userType>, scoped: handlerScope, over: handlerOverride, hsort: handlerSort): <ast> userExpr
  val (clausesAndBinders, rng2) = pOpClauses()
  val fullrange = rng.combine(rng2)
  val (clauses, binders) = extractBinders(clausesAndBinders)
  val (reinit, ret, finally, ops) = partitionClauses(clauses, fullrange)
  val hand = match (mbEff, ops)
    (Nothing, []) -> 
      val retExpr = match ret
        Nothing -> fn(x) x
        Just(f) -> fn(actionExpr) App(f, [(Nothing, App(actionExpr, [], fullrange))], fullrange)
      val handlerExpr = Lam([ValueBinder("action".new-hidden-name, Nothing, Nothing, rng, rng)], retExpr(Var("action".new-hidden-name, False, rng)), fullrange)
      binders(handlerExpr)
    _ -> binders(Handler(hsort, scoped, over, Nothing, mbEff, [], reinit, ret, finally, ops, rng, fullrange))
  applyMaybe(fullrange, reinit, finally, hand)

fun applyMaybe(rng: range, reinit: maybe<userExpr>, finally: maybe<userExpr>, f: userExpr): userExpr
  match (reinit, finally)
    (Nothing, Nothing) -> f
    _ -> 
      val applyH = App(f, [(Nothing, Var("act".new-hidden-name, False, rng))], rng)
      val bodyF = match finally
        Just(fin) -> App(Var(nameFinally, False, rng), [(Nothing, fin),(Nothing, Lam([], applyH, rng))], rng)
        Nothing -> applyH
      val bodyI = match reinit
        Just(ini) -> App(Var(nameInitially, False, rng), [(Nothing, ini), (Nothing, Lam([], bodyF, rng))], rng)
        Nothing -> bodyF
      Lam([ValueBinder("act".new-hidden-name, Nothing, Nothing, rng, rng)], bodyI, rng)

value type clause
  ClauseRet(expr: userExpr)
  ClauseFinally(expr: userExpr)
  ClauseInitially(expr: userExpr)
  ClauseBranch(expr: userHandlerBranch)

fun range(c: clause): range
  match c
    ClauseRet(e) -> e.range
    ClauseFinally(e) -> e.range
    ClauseInitially(e) -> e.range
    ClauseBranch(e) -> e.range

val userTypeRange = fn(k: userType) k.range
val userKindRange = fn(k: userKind) k.range

alias transExpr = ((userExpr) -> userExpr)
alias binder = (clause, maybe<transExpr>);
fun extractBinders(l: list<binder>)
  l.foldr(([], fn(x) x)) fn(b, acc: (list<clause>, (userExpr -> userExpr)))
    match b
      (clause, Nothing) -> (Cons(clause, acc.fst), acc.snd)
      (clause, Just(f)) -> (Cons(clause, acc.fst), fn(e) f((acc.snd)(e)))

fun partitionClauses(clauses: list<clause>, rng: range)
  fun separate(clauses': list<clause>, ret: maybe<userExpr>, fin: maybe<userExpr>, init: maybe<userExpr>, br: ctx<list<userHandlerBranch>>): <astError> (maybe<userExpr>, maybe<userExpr>, maybe<userExpr>, list<userHandlerBranch>)
    match clauses'
      Cons(ClauseRet(e), rst) -> 
        if ret.is-just then
          astError("There can be at most one 'return' clause in a handler body", e.range)
        else
          separate(rst, Just(e), fin, init, br)
      Cons(ClauseFinally(e), rst) -> 
        if fin.is-just then
          astError("There can be at most one 'finally' clause in a handler body", e.range)
        else
          separate(rst, ret, Just(e), init, br)
      Cons(ClauseInitially(e), rst) -> 
        if init.is-just then 
          astError("There can be at most one 'initially' clause in a handler body", e.range)
        else
          separate(rst, ret, fin, Just(e), br)
      Cons(ClauseBranch(e), rst) -> separate(rst, ret, fin, init, br ++ (ctx Cons(e, _)))
      Nil -> (ret, fin, init, br ++. Nil)
  separate(clauses, Nothing, Nothing, Nothing, ctx _)

fun pOpClauses()
  fun pSingleOp()
    val (op, bind) = pHandlerOp()
    ([(op, bind)], op.range)
  choices("", [
    {semiBraces("", pHandlerOpX)},
    pSingleOp,
    {val rng = pLparen(); astError("unexpected '(': local parameters are no longer supported, use a local 'var' instead", rng)},
    {([], null)}
  ])

fun pHandlerOpX()
  choices("handler clause", [
    {
      val rng = pSpecialId("finally")
      maybe("", {parens({()})})
      val expr = pBodyExpr()
      (ClauseFinally(Lam([], expr, rng.combine(expr.range))), Nothing)
    },{
      val rng = pSpecialId("initially")
      val x = parens
        choices("", [{
          val (name,prng) = pParamId()
          val tp = optionMaybe("", pTypeAnnotPar)
          (name, prng, tp)
        },{
          (new-name("_"), rng, Nothing)
        }])
      val (name, prng, tp) = x.fst
      val expr = pBodyExpr()
      (ClauseInitially(Lam([ValueBinder(name, tp, Nothing, prng, rng.combine(tp.map(fn(t) t.range).default(rng)))], expr, rng.combine(expr.range))), Nothing)
    }, pHandlerOp
  ])

fun pHandlerOp(): <ast> (clause, maybe<(userExpr -> userExpr)>)
  choicesnb("handler clause", [
    {
      val rng = pKeyword("return")
      val (name, prng, tp) = choices("", [
        {
          val (name, prng) = pParamId()
          pWarningMessage("'return x' is deprecated; use 'return(x)' instead.", prng)
          (name, prng, optionMaybe("", pTypeAnnotPar))
        },
        {
          val x = parens
            val (name, prng) = pParamId()
            (name, prng, optionMaybe("", pTypeAnnotPar))
          x.fst
        }
      ])
      val expr = pBodyExpr()
      (ClauseRet(Lam([ValueBinder(name, tp, Nothing, prng, prng.combine(tp.map(fn(t) t.range).default(prng)))], expr, rng.combine(expr.range))), Nothing)
    },{
      pKeyword("val")
      val (name, nameRng) = pQIdentifier()
      pKeyword("=")
      val expr = pBlockExpr()
      val (binder, resumeExpr) = bindExprToVal(name, nameRng, expr)
      (ClauseBranch(HandlerBranch(name.to-value-operation-name, [], resumeExpr([]), OpVal, nameRng, nameRng)), Just(binder))
    },{
      val (opSort, (name, nameRng)) = choicesnb("opSort", [
        {pKeyword("fun"); (OpFun, pQIdentifier())}, {pKeyword("ctl", ["control"]); (OpControl, pQIdentifier())}, 
        {pKeyword("final"); pKeyword("ctl"); (OpExcept, pQIdentifier())},
        {pKeyword("raw"); pKeyword("ctl"); (OpControlRaw, pQIdentifier())}, 
        // Deprecated
        {pKeyword("except"); (OpExcept, pQIdentifier())}, {pKeyword("brk"); (OpExcept, pQIdentifier())},
        {pKeyword("rcontrol"); (OpControlRaw, pQIdentifier())}, {pKeyword("rawctl"); (OpControlRaw, pQIdentifier())},
        {
          val (n, nr) = pQIdentifier(); 
          pWarningMessage("using a bare operation is deprecated.\n hint: start with 'val', 'fun', 'final ctl', 'ctl', or 'raw ctl'", nr)
          (OpControlErr, (n, nr))
        }
      ])
      val (opPars, prng) = pOpParams()
      val expr = pBodyExpr()
      (ClauseBranch(HandlerBranch(name, opPars, expr, opSort, nameRng, nameRng.combine(prng))), Nothing)
    }
  ])

fun pOpParams()
  choices("", [{parensCommas(pOpParam)}, {([], null)}])

fun pOpParam()
  val (name, rng) = pParamId()
  val tp = optionMaybe("", pTypeAnnot)
  ValueBinder(name, tp, (), rng, rng.combine(tp.map(fn(t) t.range).default(rng)))

fun pHandlerPar()
  val (name, rng) = pIdentifier()
  val tp = optionMaybe("", pTypeAnnot)
  ValueBinder(name, tp, (), rng, rng.combine(tp.map(fn(t) t.range).default(rng)))

fun pHandlerReturnDefault(r: range) // Default return clause: return(x) -> x
  val xname = "x".new-hidden-name
  val xbind = ValueBinder(xname, Nothing, Nothing, r, r)
  Lam([xbind], Var(xname, False, r), r)

fun pBranch()
  val pat = pPattern()
  val grds = pGuards()
  Branch(pat, grds)

fun pGuards()
  choicesnb("guards", [
    {pmany1("", pGuardBar)},
    {pKeyword("->"); [Guard(guardTrue, pBlockExpr())]},
    {
      val exp = pBlock()
      pWarningMessage("use '->' for pattern matches", exp.range)
      [Guard(guardTrue, exp)]
    }
  ])

fun pGuardBar()
  pBar()
  val grd = pGuardTest()
  pKeyword("->")
  val exp = pBlockExpr()
  Guard(grd, exp)

fun pGuardTest()
  choicesnb("guard condition or '_'", [
    {pSpecialId("otherwise"); astError("hint: use \"_\" instead of \"otherwise\" for the guard condition", peek().range)},
    pExpr, {pWildcard(); guardTrue}
  ])

inline fun pNtlExpr()
  pOpExprX(False)

inline fun pOpExpr()
  pOpExprX(True)

fun pOpExprX(allowTrailingLam: bool)
  val e1 = pPrefixExpr(allowTrailingLam)
  choicesnb("", [
    {
      val ess = pmany1("", {val op = pOperatorVar(); val e2 = pPrefixExpr(allowTrailingLam); [op, e2]})
      App(Var(nameOpExpr, True, null), Cons(e1, ess.concat).map(fn(e) (Nothing, e)), e1.range.combine(ess.last.map(fn(l) l.last.map(fn(m) m.range).default(e1.range)).default(e1.range)))
    }, {e1}
  ])

fun pOperatorVar()
  choicesnb("", [
    {val (name, rng) = pQOperator(); Var(name, True, rng)},
    {Var(nameAssign, True, pKeyword(":="))}
  ])

fun pPrefixExpr(allowTrailingLam: bool): <ast> userExpr
  val ops = pmany("", pPrefixOp)
  val aexp = pAppExpr(allowTrailingLam)
  ops.foldr(aexp, fn(op, e) App(op, [(Nothing, e)], op.range.combine(e.range)))

fun pAppExpr(allowTrailingLam: bool): <ast> userExpr
  val e0 = pAtom()
  val fs = pmany("", {choices("", [pDotExpr, pApplier, pIndexer, {pFunApps(allowTrailingLam)}])})
  fs.foldl(e0, fn(e, f) f(e))

fun pDotExpr(): <ast> (userExpr -> userExpr)
  pKeyword(".")
  val e = pAtom()
  choicesnb("", [
    {
      val rng0 = pLapp()
      val args = pSepBy("", pArgument, pComma)
      val rng1 = pRparen()
      fn(arg0) App(e, Cons((Nothing, arg0), args), rng0.combine(rng1))
    },
    {
      fn(arg0) App(e, [(Nothing, arg0)], arg0.range.combine(e.range))
    }
  ])

fun pIndexer(): <ast> (userExpr -> userExpr)
  val rng0 = pLidX()
  choicesnb("", [
    {
      val crng = pKeyword("ctx")
      val ct = pCcontext(crng)
      val rng1 = pSpecial("]")
      fn(e)
        val rng = e.range.combine(rng1)
        App(Var(nameCCtxComposeExtend, False, rng1), [(Nothing, e), (Nothing, ct)], rng1)
    },
    {
      val idxs = pSepBy1("", pExpr, pComma)
      val rng1 = pSpecial("]")
      fn(e) App(Var(nameIndex, False, rng0.combine(rng1)), Cons(e, idxs).map(fn(a) (Nothing, a)), rng0.combine(rng1))
    }
  ])

fun pApplier(): <ast> (userExpr -> userExpr)
  val rng0 = pLapp()
  val args = pSepBy("", pArgument, pComma)
  val rng1 = pRparen()
  fn(e) App(e, args, rng1.combine(e.range))

fun pFunApp(allowTrailingLam: bool): <ast> userExpr
  if allowTrailingLam then choices("", [pFunBlock, {pLambda([])}])
  else pLambda([])

fun pFunApps(allowTrailingLam): <ast> (userExpr -> userExpr)
  fun injectApply(e, fs)
    match fs
      [] -> e
      _ -> 
        val nfargs = fs.map(fn(e') (Nothing, e'))
        match e
          App(f, args, rng) -> App(f, args ++ nfargs, rng)
          _ -> App(e, nfargs, e.range.combine(nfargs.last.map(fn(e') e'.snd.range).default(e.range)))
  val fs = pmany1("", {pFunApp(allowTrailingLam)})
  fn(arg0)
    injectApply(arg0, fs)

fun pArgument()
  val exp = pAExpr()
  match exp
    Var(name, _, rng) ->
      val x = maybe("=")
        pKeyword("=")
        (Just((name, rng)), pExpr())
      match x
        Just(x') -> x'
        Nothing -> (Nothing, exp)
    _ -> (Nothing, exp)

/// Atomic expression
fun pAtom()
  choicesnb("(simple) expression", [
    {val (name, rng) = choicesnb("", [pQIdentifier, pQConstructor]); Var(name, False, rng)},
    pTupleExpr, pListExpr, {Literal(pLiteral())}, pCCtxHole, pCCtxExpr, pInjectExpr
  ])

fun pLiteral()
  choicesnb("", [
    {val (i, tok) = pInteger(); LitInt(i, tok.range)},
    {val (f, tok) = pFloat(); LitFloat(f, tok.range)},
    {val (s, range) = pStringLit(); LitString(s, range)},
    {val (c, range) = pCharLit(); LitChar(c.string, range)},
  ])

fun pAExpr()
  val e = pExpr()
  choicesnb("", [{pKeyword(":"); val tp = pTypeScheme(); Ann(e, tp, e.range.combine(tp.range))}, {e}])

fun pTupleExpr()
  val rng1 = pLparen()
  val es = pSepBy("", pAExpr, pComma)
  val rng2 = pRparen()
  val rng = rng1.combine(rng2)
  match es
    Nil -> Var(nameUnit, False, rng)
    [e] -> Parens(e, nil, rng)
    _ -> App(Var(name-tuple(es.length), False, rng), es.map(fn(e) (Nothing, e)), rng)

fun pListExpr(): <ast> userExpr
  val rng1 = pSpecial("[")
  val es = pSepBy("",pAExpr, pComma)
  val rng2 = pSpecial("]")
  if es.is-nil then
    makeNil(rng1.combine(rng2))
  else
    es.foldr(makeNil(rng2.after), fn(x, acc) rng1.makeCons(x, acc, userTypeRange)).adjustRange(rng1.combine(rng2))

fun makeNil(r: range)
  makeApp(Var(nameNull, False, r), [], userTypeRange)

fun makeCons(r: range, x: expr<t>, xs: expr<t>, rT: (t) -> range): expr<t>
  makeApp(Var(nameCons, False, r), [x, xs], rT)

fun pCCtxExpr()
  pCcontext(pKeyword("ctx"))

fun pCcontext(rng: range)
  makeApp(Var(nameCCtxCreate, False, rng), [pNtlExpr()], userTypeRange)

fun pCCtxHole(): <ast> userExpr
  val rng = choices("", [{pKeyword("hole")}, {pWildcard().snd}])
  makeApp(Var(nameCCtxHoleCreate, False, rng), [], userTypeRange)

fun pInjectExpr()
  val (rng, mkInj) = injectType()
  choicesnb("", [
    {mkInj(parens({choices("", [pExpr, pFunBlock])}).fst)},
    {val name = new-hidden-name("mask-action"); Lam([ValueBinder(name, Nothing, Nothing, rng, rng)], mkInj(Var(name, False, rng)), rng)}
  ])

fun injectType()
  val rng1 = pKeywordInject()
  val behind = choicesnb("", [{choices("", [{pSpecialId("behind")}, {pSpecialId("other")}]); True}, {False}])
  pLangle()
  val tp = pType()
  pRangle()
  (rng1, fn(exp) Inject(promoteType(tp), exp, behind, rng1.combine(exp.range)))

fun pBinder(pre: range)
  val (name, range) = pIdentifier()
  val ann = pTypeAnnotation()
  fn(e) ValueBinder(name, (), ann(e), range, pre.combine(range))

inline fun pPattern(): <ast> userPattern
  pPatAnn()

fun pPatAnn(): <ast> userPattern
  val p = pPatAtom()
  pMaybeTypeAnnot(p) fn(tp0)
    val tp = promoteType(tp0)
    match p
      PatVar(ValueBinder(name, Nothing, npat, rng1, rng2)) -> PatVar(ValueBinder(name, Just(tp), npat, rng1, rng2))
      _ -> PatAnn(p, tp, p.range.combine(tp.range))

fun pPatAtom()
  choicesnb("pattern atom", [
    {
      val (name, rng) = pQConstructor()
      val (ps, r) = choicesnb("", [{parensCommas(pNamedPattern)}, {([], null)}])
      PatCon(name, ps, rng, rng.combine(r))
    },
    {
      val (name, rng) = pIdentifier()
      choices("", [
        {pKeyword("as"); val p = pPattern(); PatVar(ValueBinder(name, Nothing, p, rng, rng.combine(p.range)))},
        {PatVar(ValueBinder(name, Nothing, PatWild(rng), rng, rng))}
      ])
    },
    {PatWild(pWildcard().snd)},
    {PatLit(pLiteral())},
    {pListPattern()},
    {
      val (ps, rng) = parensCommas(pNamedPattern);
      match ps
        [(_, p)] -> PatParens(p, rng)
        _ -> PatCon(name-tuple(ps.length), ps, rng, rng)
    }
  ])

fun pNamedPattern()
  choices("named pattern", [
    {
      val (name, rng) = pIdentifier();
      pKeyword("=")
      (Just((name, rng)), pPattern())
    },
    { (Nothing, pPattern()) }
  ])

fun pMaybeTypeAnnot(d: a, f: (userType) -> div a): <ast> a
  choices("", [{f(pTypeAnnot())}, {d}])

fun pListPattern()
  val rng1 = pSpecial("[")
  val es = pSepBy("", pPattern, pComma)
  val rng2 = pSpecial("]")
  if es.is-nil then
    makeNilPat(rng1.combine(rng2))
  else
    PatParens(es.foldr(makeNilPat(rng2.after), fn(x, acc) makeConsPat(x, acc)), rng1.combine(rng2))

fun makeNilPat(rng)
  PatCon(nameNull, [], rng, rng)

fun makeConsPat(x, xs)
  PatCon(nameCons, [(Nothing, x), (Nothing, xs)], x.range, x.range)

fun pTypeAnnot()
  pKeyword(":")
  pType()

fun pTypeAnnotPar()
  pKeyword(":")
  choicesnb("", [
    {
      val rng = pSpecialOp("?")
      val tp = pType()
      TpApp(TpCon(nameTpOptional, rng), [tp], rng.combine(tp.range))
    },
    {
      val rng = pSpecialOp("$")
      val (eff, res) = pTResultTotal()
      TpApp(TpCon(nameTpDelay, rng), [eff, res], rng.combine(res.range))
    },
    pType
  ])

fun pTypeScheme()
  promoteType(choices("type signature", [pQuanSome, pType]))

fun pType(): <ast> userType
  choices("type", [pQuanForall, pQuanSome, pTQual])

fun aQuantifier()
  maybeList({pKeyword("forall"); parens(pTBinders).fst})

fun sQuantifier()
  maybeList({pKeyword("some"); parens(pTBinders).fst})

fun pQuanSome()
  pQuantifier(QSome, pType)

fun pQuanForall() 
  pQuantifier(QForall, pTQual)

fun pQuanExists()
  pQuantifier(QExists, pType)

fun pQuantifier(quan: userQuantifier, next)
  val rng = pKeyword(if quan.is-qsome then "some" else if quan.is-qexists then "exists" else "forall")
  val params = angles(pTBinders).fst
  val tp = next()
  params.foldr(tp, fn(name, t) TpQuan(quan, name, t, rng.combine(t.range)))

fun pTQual()
  pQualifier(pTArrow())

fun pQualifier(tp: userType)
  choices("", [
    {
      pKeyword("with")
      TpQual(parens({pmany1("", pPredicate)}).fst, tp)
    },
    {tp}
  ])

fun pPredicate()
  choices("predicate", [{pTypeApp(pTId())}])

fun pTArrow(): <ast> userType
  val (tps, rng1) = pTAtom()
  choices("", [
    {pKeyword("->"); val (teff, tres) = pTResultTotal(); TpFun(tps, teff, tres, rng1.combine(tres.range))},
    {tuple(tps, rng1)}
  ])

fun pTEffect(): <ast> userType
  val rng1 = pLangle()
  val labels:list<userType> = pSepBy("", pTLabel, pComma)
  val (ext, brng) = pTExtend()
  val rng = pRangle()
  labels.foldr(ext(rng), fn(x, acc) makeEffectExtend(x, acc, brng))

fun pTExtend()
  choices("", [
    {val brng = pBar(); val tp = choices("", [pTEffect, pTId]); (fn(x) tp, brng)},
    {(makeEffectEmpty, null)}
  ])

fun pTLabel()
  pTypeApp(pTId())

fun pTResultTotal()
  val (mbeff, tres) = pTResult()
  val teff = mbeff.default(makeTpTotal(tres.range.before))
  (teff, tres)

fun pTResult(): <ast> (maybe<userType>, userType)
  val (tps1, rng1) = pTAtom()
  choices("", [{val (tps, rng) = pTAtom(); (Just(tuple(tps1, rng)), tuple(tps, rng))}, {(Nothing, tuple(tps1, rng1))}])

fun pTAtomic()
  val (ts, rng) = pTAtom()
  tuple(ts, rng)

fun tuple(tps: list<(name, userType)>, r: range): userType
  match tps
    Cons(tp, Nil) -> tp.snd
    _ -> TpApp(TpCon(name-tuple(tps.length), r), tps.map(snd), r)

fun pTAtom()
  fun single(tp: userType)
    ([(nil, tp)], tp.range)
  fun mkTuple(n: int, rng: range)
    TpCon(name-tuple(n).unqualify, rng)
  choices("type atom", [
    {val tp1 = pTId(); val tp2 = pTypeApp(tp1); single(tp2)},
    {
      val rng1 = pLparen()
      choices("", [
        {
          val tps = pSepBy("", pParamTypeX, pComma)
          val rng2 = pRparen()
          (tps.map(fn((name, _, tp)) (name, tp)), rng1.combine(rng2))
        },
        {
          val cs = pmany1("", pComma)
          val rng2 = pRparen()
          val tp = pTypeApp(mkTuple(cs.length + 1, rng1.combine(rng2)))
          single(tp)
        }
      ])
    },
    { single(pTEffect()) }
  ])

fun pTypeApp(tp: userType)
  choices("", [
    {
      val rng1 = pLangle()
      val targs = pSepBy("", pAnnTypeK, pComma)
      val rng2 = pRangle()
      TpApp(tp, targs, tp.range.combine(rng2).combine(rng1))
    },
    {tp}
  ])

fun pParamType(): <ast> (name, range, userType)
  val (id, rng) = choices("", [pVarId, pWildcard, {(nil, null)}])
  pKeyword(":")
  val tp = pParameterType(rng)
  (id, rng, tp)

fun pParamTypeX(): <ast> (name, range, userType)
  choices("parameter type", [
    {
      val (id, rng) = try("", {val x = choices("", [pVarId, pWildcard]); pKeyword(":"); x})
      val tp = pParameterType(rng)
      (id, rng, tp)
    },
    {
      val tp = pParameterType(null)
      (nil, tp.range, tp)
    }
  ])

fun pParameterType(r: range)
  choices("parameter type", [
    {
      val rng2 = pSpecialOp("?")
      val tp = pType()
      TpApp(TpCon(nameTpOptional, r), [tp], rng2.combine(tp.range))
    },
    pType
  ])

fun pAnnTypeK()
  val tp = pType()
  choices("TypeAnnotation", [
    {pSpecialOp("::"); TpAnn(tp, pKind())},
    {tp}
  ])

fun pTId()
  val (id, rng) = choices("Type", [pQVarId, pTypeIdCtx, pWildcard])
  if id.is-wildcard || id.isTypeVar then TpVar(id, rng) else TpCon(id, rng)

fun makeApp(expr: expr<t>, args: list<expr<t>>, rT: (t) -> range): expr<t>
  App(expr, args.map(fn(a) (Nothing, a)), expr.range.combine(args.last.map(range).default(expr.range)))

fun makeTpPure(rng: range): kUserType<k>
  TpCon(nameTpPure, rng)

fun makeTpTotal(rng: range): kUserType<k>
  TpCon(nameEffectEmpty, rng)

fun makeEffectEmpty(rng: range): kUserType<k>
  TpCon(nameEffectEmpty, rng)

fun makeEffectExtend(label: kUserType<k>, ext: kUserType<k>, rng: range = null, ?range: (k) -> range): kUserType<k>
  TpApp(TpCon(nameEffectExtend, rng), [label, ext], label.range.combine(ext.range))

fun pTBinderDef()
  val (id, rng) = pTBinderId()
  fn(k) TypeBinder(id, k, rng, rng)

fun pTBinders()
  pSepBy("type binder", pTBinder, pComma)

fun pTBinder()
  val (id, rng) = pVarId()
  val kind = pKindAnnot()
  return TypeBinder(id, kind, rng, rng)

fun pKindAnnot()
  choices("kind", [{
    pSpecialId("::")
    pKind()
  },
  {KindNone}])

fun pKind()
  choices("kind", [
   {
    val (params, _) = parensCommas(pKind)
    pKeyword("->")
    val res = pKind()
    params.foldr(res, fn(a, acc) KindArrow(a, acc))
   },
   {
    val k = pKindAtom()
    choices("kind", [{
      pKeyword("->")
      val k2 = pKind()
      KindArrow(k, k2)
    }, {k}])
   }
  ])

fun pKindAtom()
  choicesnb("kind constant (V,E,H,S,X,HX,HX1, or P)", [
   {
    val (k, rng) = parens(pKind)
    KindParens(k, rng)
   },
   { KindCon(nameKindStar, pSpecialConId("V")) },
   { KindCon(nameKindLabel, pSpecialConId("X")) },
   { KindCon(nameKindEffect, pSpecialConId("E")) },
   { KindCon(nameKindHeap, pSpecialConId("H")) },
   { KindCon(nameKindScope, pSpecialConId("S")) },
   { KindCon(nameKindPred, pSpecialConId("P")) },
   { KindCon(nameKindHandled, pSpecialConId("HX")) },
   { KindCon(nameKindHandled, pSpecialConId("HX1")) }
  ])

fun warnDeprecated(o: string, n: string, rng: range): <ast> ()
  addWarning("warning " ++ rng.start.show ++ ": keyword \"" ++ o ++ "\" is deprecated, use \"" ++ n ++ "\" instead", rng)

fun pWarningMessage(msg: string, rng: range)
  addWarning("warning " ++ rng.start.show ++ ":" ++ msg, rng)

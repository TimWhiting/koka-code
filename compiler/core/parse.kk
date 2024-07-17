import std/os/path
import std/os/file
import std/data/linearmap
import compiler/common/parse
import compiler/common/id
import compiler/syntax/lexeme
import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/common/name-prim
import compiler/common/syntax
import compiler/common/failure
import compiler/kind/kind
import compiler/kind/synonyms
import compiler/kind/importmap
import compiler/type/type
import compiler/type/assumption
import compiler/platform/config
import compiler/core/core
import compiler/type/typevar

fun parseCore(fname: path)
  val input = read-text-file(fname)
  lexParse(False, fn(lexes) lexes.allowDotIds.requalify, {pProgram(Source(fname.string, input))}, fname.string, input)

fun requalify(lexes: list<lexeme>): div list<lexeme>
  match lexes
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexId(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexIdOp(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexOp(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexCons(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexCons(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(lex, lexx)
      -> Cons(lex, requalify(lexx))
    [] -> []

fun allowDotIds(lexes: list<lexeme>): div list<lexeme>
  match lexes
    // Identifier
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexId(nm)), lexx)) -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(prepend(".", nm))), lexx))
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexWildCard(nm)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2),  LexWildCard (".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexId(nm)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId (postpend("." ++ i.show, nm))), lexx))
    // operator
    Cons(Lexeme(r1, LexKeyword(".")),Cons(Lexeme(r2, LexOp(nm)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexOp(nm)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId(postpend("." ++ i.show, nm))), lexx))

    // constructor
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexCons(nm)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexCons(".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexCons(nm)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexCons(postpend("." ++ i.show, nm))), lexx))

    // (-.4), (++.2)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(nm)), Cons(Lexeme(_,LexInt(i)), Cons(Lexeme(r5,LexSpecial(")")), lexx)))) // | last (nmId nm) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(postpend(i.show, nm))), lexx))
    // (/.4)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(nm)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r5, LexSpecial(")")), lexx))))) // | last (nmId nm) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(postpend("." ++ i.show, nm))), lexx))
    // ([].1)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")),Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(_, LexKeyword(".")),Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r2, LexSpecial(")")), lexx))))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(postpend("." ++ i.show, "[]".newName))), lexx))
    // ([])
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")), Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(r2, LexSpecial(")")), lexx))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId("[]".newName)), lexx))
    Cons(l, lx) -> Cons(l, allowDotIds(lx))
    Nil -> Nil

fun parseInlines(prog: core, s: source, env: envv, inlines: list<lexeme>, gamma: gamma)
  with parseLexemes(s, inlines)
  with withEnvInitial(prog.coreName, emptyImports)
  setEnv(env(gamma=gamma))
  val idefs = pmany("inline", pInlineDef)
  peof()
  idefs

fun pProgram(s: source)
  pmany("semis", pSemicolon)
  val (prog, env, inlines) = pModule()
  peof()
  (prog, fn(gamma) parseInlines(prog, s, env, inlines, gamma))

fun pModule()
  val (_, doc) = pDocKeyword("module")
  pKeyword("interface")
  val (name0, _) = pModulePath()
  pmany("semis", pSemicolon)
  braced
    val (imps, impAliases) = semis("import", pImportDecl).unzip
    val impMap = impAliases.foldr(emptyImports) fn((asname, name'), m) 
      match m.importsExtend(asname, name')
        Just(imp') -> imp'
        Nothing -> m
    val externImports = semis("extern imports", pExternImportDecl)
    val fixs = semis("fix decls", pFixDecl)
    with withEnvInitial(name0, impMap)
    val impsyns = semis("import synonyms", pLocalAlias)
    val tdefs = semis("type decls", pTypeDecl)
    val defs = semis("fun decls", pDefDecl)
    val externs = semis("externs", pExternDecl)
    val inlines = maybe("inlines", {pSpecial("//.inline-section"); val rest = takeAll(); putAll([]); rest}).default([]) // TODO: Read rest
    val tdefGroups = tdefs.map(fn(tdef) [tdef])
    val defGroups = defs.map(DefNonRec)
    (Core(name0, imps, fixs.concat, tdefGroups, defGroups, externImports ++ externs, doc), getEnv(), inlines)

fun pLocalAlias()
  try("local alias", {pSpecialId("local"); pKeyword("alias")})
  val qname = pQTypeId().fst
  val name = envQualify(qname)
  val params = pTypeParams()
  val kind = pKindAnnotFull()
  pKeyword("=")
  val tp = pType()
  val rank = maybe("", {pKeyword("="); pInteger().fst}).default(0)
  val syn = SynInfo(name, kind, params, tp, rank, rangeNull, Private, "")
  envExtendSynonym(syn)
  syn

fun pVisPub()
  maybe("visibility", {pKeyword("pub"); Public}).default(Private)

fun pImportDecl(): <ast> (compiler/core/core/kimport, (name, name))
  val (vis, doc) = try("import", {(pVisPub(), pDocKeyword("import").snd)})
  val (asname, name, _) = pImportAlias()
  val pkg = maybe("=", {pKeyword("="); pStringLit().fst}).default("")
  (compiler/core/core/Kimport(name, pkg, vis, doc), (asname, name))

fun pFixDecl()
  val fix = pFixity()
  val op = pIdentifier().fst
  [FixDef(op, fix)]

fun pFixity()
  val assoc = choices("assoc", [
    {pKeyword("infixl"); AssocLeft},
    {pKeyword("infixr"); AssocRight},
    {pKeyword("infix"); AssocNone}
  ])
  val (prec, _) = pInteger()
  FixInfix(prec, assoc)

fun pTypeDecl()
  choices("type decl", [
    {
      val (vis, (ddef, isExtend, sort, doc)) = try("visibility", {(pVisPub(), pTypeSort())})
      val tn = if isExtend then
          pQTypeId().fst
        else
          qualify(modname, choices("identifier", [pTBinderId, pIdOp]).fst)
      val params = pTypeParams()
      val kind = pKindAnnotFull()
      val cons = maybe("constructor", {semiBraces("contructor args", {pConDecl(tn, params, sort)}).fst}).default([])
      val cons1 = match cons
        [con1] -> [con1(singleton=True)]
        _ -> cons
      val dataInfo = DataInfo(sort, tn, kind, params, cons1, rangeNull, ddef, vis, doc)
      Data(dataInfo, isExtend)
    },{
      val (vis, doc) = try("visibility", {(pVisPub(), pDocKeyword("alias").snd)})
      val name = pTBinderId().fst
      val params = pTypeParams()
      val kind = pKindAnnotFull()
      pKeyword("=")
      val tp = pType()
      val rank = maybe("rank", {pKeyword("="); pInteger().fst}).default(0)
      val qname = qualify(modname, name)
      val syn = SynInfo(qname, kind, params, tp, rank, rangeNull, vis, doc)
      envExtendSynonym(syn)
      Synonym(syn)
    }
  ])

fun pConDecl(tname0: name, foralls: list<typeVar>, sort: dataKind)
  val (vis, doc) = try("visibility", {(pVisPub(), pDocKeyword("con").snd)})
  val name = pConstructorId().fst
  val exists0 = pTypeParams()
  val params = pParameters()
  val vrepr = pValueRepr()
  val tp = pTypeAnnot()
  val params2 = params.zip(list(1, params.length)).map(fn(((n, t), i)) (if n.nameStem == "" then i.newFieldName else name, t))
  val orderedFields = []
  ConInfo(qualify(modname, name), tname0, foralls, exists0, params2, tp, sort, rangeNull, params2.map(fn(_) rangeNull), params2.map(fn(_) Public), False, orderedFields, vrepr, vis, doc)

fun pTypeSort()
  val isRec = maybe("recursive", {pSpecialId("recursive")}).is-just
  val (ddef0, isExtend, sort) = pTypeMod()
  val doc = pDocKeyword("type").snd
  val ddef = match (isRec, ddef0)
    (True, DataDefNormal) -> DataDefRec
    _ -> ddef0
  (ddef, isExtend, sort, doc)

fun pTypeMod()
  choices("type modifier", [
    {pSpecialId("open"); (DataDefOpen, False, Inductive)},
    {pSpecialId("extend"); (DataDefOpen, True, Inductive)},
    {pSpecialId("value"); (DataDefValue(pValueRepr()), False, Inductive)},
    {pSpecialId("co"); (DataDefNormal, False, CoInductive)},
    {pSpecialId("rec"); (DataDefNormal, False, Retractive)},
    {(DataDefNormal, False, Inductive)}
  ])

fun pValueRepr()
  braced
    val rraw = pInteger().fst
    pComma()
    val scan = pInteger().fst
    pComma()
    val align = pInteger().fst
    ValueRepr(rraw, scan, align)

fun pDefDecl()
  val (vis, sort0, inl, doc) = try("visibility and sort", {val vis = pVisPub(); val (sort, inl, _, doc) = pDefSort(); (vis, sort, inl, doc)})
  val (name, _) = choices("decl name", [pFunId, pIdOp])
  pKeyword(":")
  val (tp, pinfos) = pDefType()
  val sort = match sort0
    DefFun(_, fipT) -> DefFun(pinfos, fipT)
    _ -> sort0
  Def(qualify(modname, name), tp, ELit(LitString("core/parse " ++ name.show ++ ": cannot get the expression from an interface core file")), vis, sort, inl, rangeNull, doc)

fun pDefSort()
  val isRec = maybe("recursive", {pSpecialId("recursive")}).is-just
  val inl = pInline()
  choices("fip info", [
    {
      val fipT = try("fip", pFip)
      val (_, doc) = pDocKeyword("fun")
      choices("specialization", [{pSpecialOp("**"); ()}, {pSpecialOp("*"); ()}, {()}])
      (defFunEx([], fipT), inl, isRec, doc)
    },
    {(DefVal, inl, False, pDocKeyword("val").snd)}
  ])

fun pInlineDef()
  val (sort, inl, isRec, specArgs, _) = pInlineDefSort()
  val (name, _) = pFunId()
  val e = pBody()
  InlineDef(envQualify(name), e, isRec, inl, if inl.is-inlineAlways then 0 else e.cost, sort, specArgs)

fun pExternDecl()
  val (vis, fipT, doc) = try("visibility", {(pVisPub(), pFip(), pDocKeyword("extern").snd)})
  val (name, rng) = pFunId()
  pKeyword(":")
  val (tp, pinfos) = pDefType()
  val formats = pExternalBody()
  External(qualify(modname, name), tp, pinfos, formats, vis, fipT, rng, doc)

fun pExternalBody()
  choices("external body", [
    {pKeyword("="); [pExternalEntry()]},
    {semiBraces("external entry", pExternalEntry).fst}
  ])

fun pExternalEntry()
  val target = pExternalTarget()
  maybe("external inline", {pSpecialId("inline")})
  val s = pStringLit().fst
  (target, s)

fun pExternalTarget()
  choices("external target", [
    {pSpecialId("c"); C(CDefault)},
    {pSpecialId("cs"); CS},
    {pSpecialId("js"); JS(JsDefault)},
    {DefaultTarget}
  ])

fun pExternImportDecl()
  try({pKeyword("extern"); pKeyword("import")})
  ExternalImport(pExternalImportBody(), rangeNull)

fun pExternalImportKeyVal()
  val key = pStringLit().fst
  pKeyword("=")
  val v = pStringLit().fst
  (key, v)

fun pExternalImportEntry()
  val target = pExternalTarget()
  (target, semiBraces("external key value", pExternalImportKeyVal).fst)

fun pExternalImportBody()
  choices("external import body", [
    {
      pKeyword("=")
      [pExternalImportEntry()]
    },
    {
      semiBraces("external import entries",pExternalImportEntry).fst
    }
  ])

fun pInlineDefSort()
  val isRec = maybe("inline recursive", {pSpecialId("recursive")}).is-just
  val inl = pInline()
  val spec = maybe("inline specialize", {pSpecialId("specialize"); val (s,_) = pStringLit(); s.list.map(fn(c) c == '*')}).default([])
  val pinfos = maybe("inline borrow", {pSpecialId("borrow"); val (s, _) = pStringLit(); s.list.map(fn(c) if c == '^' then Borrow else Own)}).default([])
  choices("fun or val inline", [
    {
      val f = pFip()
      val (_, doc) = pDocKeyword("fun")
      (DefFun(pinfos, f), inl, isRec, spec, doc)
    },
    {
      val (_, doc) = pDocKeyword("val")
      (DefVal, inl, False, spec, doc)
    }
  ])

fun pBody()
  pKeyword("=")
  val e = pExpr()
  optionMaybe("semis", pSemicolon)
  e

fun pExpr()
  choices("expr", [pFun, pForall, pMatch, pLet, pApp])

fun pApp(): <ast,eenv,comp-flags,synonyms> expr
  val expr = pAtom()
  fun parseApplies(e)
    choices("app", [
      {
        val args = parensCommas(pExpr).fst
        parseApplies(App(e, args))
      },
      {
        val tps = angles({pSepBy("expr args", pType, pComma)}).fst
        parseApplies(TypeApp(e, tps))
      },
      {e}
    ])
  parseApplies(expr)

fun pAtom()
  choices("atom", [pCon, pVar, {ELit(pLit())}, {parens(pExpr).fst}])

fun pLet()
  val dgs = pDefGroups()
  Let(dgs, pExpr())

fun pForall()
  pKeyword("forall")
  val tvars = pTypeParams1()
  TypeLam(tvars, pExpr())

fun semiBraced(n, p)
  pLcurly()
  pmany(n, pSemicolon)
  val x = p()
  pmany(n, pSemicolon)
  pRcurly()
  x

fun pFun()
  pKeyword("fn")
  val eff = maybe("type parameters", {angles(pType).fst}).default(typeTotal)
  val params = pParameters()
  val body = semiBraced("fun", pExpr)
  Lam(params.map(fn((n, t)) TName(n, t)), eff, body)

fun pMatch()
  pKeyword("match")
  val args = parensCommas(pExpr).fst
  val branches = semiBraces("match branches", pBranch).fst
  Case(args, branches)

fun pCon()
  val name = pQualifiedConId()
  val InfoCon(_, typ, repr) = envLookupCon(name)
  Con(TName(name, typ), repr)

fun pVar()
  val name = choices("var identifier", [pQVarId, pQIdOp]).fst
  if name.isQualified then
    envLookupVar(name)
  else
    val tp = envLookupLocal(name)
    Var(TName(name, tp), InfoNone)

fun pLit()
  choices("literal", [
    {LitInt(pInteger().fst)},
    {LitFloat(pFloat().fst)},
    {LitString(pStringLit().fst)},
    {LitChar(pCharLit().fst)},
  ])

fun pDefGroups()
  val dg = pDefGroup()
  val dgs = pDefGroups0()
  Cons(dg, dgs)

fun pDefGroups0()
  maybe("def groups", {pDefGroups()}).default([])  

fun pDefGroup(): <ast,eenv,comp-flags,synonyms> defGroup
  val (sort, inl, _, doc) = pDefSort()
  val (name, _) = choices("def group", [pFunId, {pWildcard(); (nameNil, rangeNull)}])
  val tp = pTypeAnnot()
  val expr = pBody()
  envExtendLocal(name, tp)
  DefNonRec(Def(name, tp, expr, Private, sort, inl, rangeNull, doc))

fun pBranch()
  val patts = pPatterns1()
  val guards = pmany1("guard", pGuard)
  Branch(patts, guards)

fun pPatterns1()
  val pat = pPattern()
  maybe("pattern comma", {pComma(); Cons(pat, pPatterns1())}).default([])

fun pGuard()
  val grd = maybe("guard expr", {pBar(); try("guard", pExpr)}).default(exprTrue)
  pKeyword("->")
  Guard(grd, pExpr())

fun pPattern()
  val pat = pPatternBasic()
  maybe("as", {pKeyword("as"); pPatVar(pat)}).default(pat)

fun pPatternBasic()
  choices("pattern", [pPatCon, {pPatVar(PatWild)}, pPatLit, pPatWild, {parens(pPattern).fst}])

fun pPatCon()
  val skip = maybe(".skip", {pSpecialId(".skip")}).is-just
  val cname = pQualifiedConId()
  val exists0 = pTypeParams()
  val args = try("pattern args", {pLparen(); val x = pPatternArgs0(); pRparen(); x})
  val (patArgs, argTypes) = args.unzip
  val resTp = pTypeAnnot()
  val InfoCon(_, typ, repr, cons) = envLookupCon(cname)
  PatCon(TName(cname, typ), patArgs, repr, argTypes, exists0, resTp, cons, skip)

fun pPatternArgs0(): <ast,eenv,comp-flags,synonyms> list<(pattern, ktype)>
  maybe("pattern args", {pPatternArgs1()}).default([])

fun pPatternArgs1()
  val pattp = pPatternArg()
  maybe("pattern args", {pComma(); Cons(pattp, pPatternArgs1())}).default([])

fun pPatternArg()
  val pat = pPattern()
  val tp = pTypeAnnot()
  (pat, tp)

fun pPatVar(pat: pattern)
  val (name, _) = pVarId()
  val tp = pTypeAnnot()
  envExtendLocal(name, tp)
  PatVar(TName(name, tp), pat)

fun pPatLit()
  PatLit(pLit())

fun pPatWild()
  pWildcard()
  PatWild

fun pQualifiedConId()
  choices("constructor id", [
    {
      pModulePath()
      pSpecialOp("/")
      pSpecial("(")
      val cs = pmany("comma", pComma)
      pSpecial(")")
      nameTuple(cs.length + 1)
    },
    {pQConId().fst}
  ])

fun pParameters()
  val iparams = maybe("parameters", {parensCommas({pParameter(False)}).fst}).default([])
  val (params, _) = iparams.unzip
  params.map(fn((n, t)) envExtendLocal(n, t))
  params

fun pParameter(allowBorrow: bool)
  val (name, pinfo) = maybe("parameter info", {
    val pinfo = if allowBorrow then pParamInfo() else Own
    val (name, _) = pParamId()
    pKeyword(":")
    (name, pinfo)
  }).default((nameNil, Own))
  choices("optional type", [
    {
      pSpecialOp("?")
      ((name, makeOptional(pType())), pinfo)
    },
    {
      ((name, pType()), pinfo)
    }
  ])

fun pTypeAnnot()
  pKeyword(":")
  pType()

fun pTypeAnnotFull()
  pSpecialOp("::")
  pType()

fun pTypeParams()
  maybe("type parameters", pTypeParams1).default([])

fun pTypeParams1()
  angles(pTBinders).fst

fun pTBinders()
  val bs = pSepBy("quantifiers", pTBinder, pComma)
  bs.map fn((name, kind)) 
    envExtend(name, kind)
    match envType(name, kind)
      TVar(tv) -> tv
      _ -> fail("core/parse pTBinders: expecting type variable")

fun pTBinder()
  choices("quantifier", [
    {
      val id = choices("type parameter", [pVarId, pWildcard]).fst
      val kind = pKindAnnotFull()
      (id, kind)
    },
    {
      parens(pTBinder).fst
    }
  ])

fun pKindAnnotFull()
  pKindAnnot()

fun pKindAnnot()
  maybe("kind annotation", {pSpecialOp("::"); pKind()}).default(kindStar)

fun pType(): <ast,eenv,comp-flags,synonyms> ktype
  pTypeX(False).fst

fun pDefType()
  val (tp, pinfos) = pTypeX(True)
  (tp, if pinfos.all(is-own) then [] else pinfos)

fun pTypeX(allowBorrow: bool)
  try("type")
    val quantify = pTForall()
    val (tp, pinfos) = pTArrow(allowBorrow)
    val preds = pQualifier()
    (quantify(preds, tp), pinfos)

fun pTForall()
  val params = maybe("type forall", {pKeyword("forall"); pTypeParams1()})
  fn(ps, rho)
    if ps.is-nil then rho else TForAll(params.default([]), ps, rho)

fun pQualifier()
  maybe("qualifier", {pKeyword("with"); pmany1("qualifier predicates", pPredicate)}).default([])

fun pPredicate(): <ast,eenv,comp-flags,synonyms> pred
  try("predicate") 
    val (name, _) = pQVarId()
    val tps = maybe("predicate type parameters", {angles({pSepBy("predicates", pType, pComma)}).fst}).default([])
    PredIFace(envQualify(name), tps)  

fun pTArrow(allowBorrow: bool)
  val etp = pTAtomParams(allowBorrow)
  match etp
    Left((params, pinfos)) ->
      choices("function type", [
        {
          pKeyword("->")
          (pTResult(params), pinfos)
        },
        {
          val tp = extract(params, "unexpected parameters not followed by an ->")
          (pTypeApp(tp), pinfos)
        }
      ])
    Right(tp) -> (tp, [])

fun pTResult(params)
  val tp1 = pTAtom()
  val res = maybe("result type")
    TFun(params, tp1, pTAtom())
  match res
    Just(tp) -> tp
    Nothing -> TFun(params, typeTotal, tp1)

fun pTAtom(): <ast,eenv,comp-flags,synonyms> ktype
  val etp = pTAtomParamsEx(False, False)
  match etp
    Left((params, _)) -> pTypeApp(extract(params, "expecting single type"))
    Right(tp) -> tp

fun extract(params, msg)
  match params
    Nil -> typeUnit
    [(name, tp)] | name == nameNil -> tp
    _ -> 
      if params.all(fn(n) n.fst == nameNil) then
        TApp(typeTuple(params.length), params.map(snd))
      else
        fail(msg)

fun pTAtomParams(allowBorrow: bool)
  pTAtomParamsEx(True, allowBorrow)

fun pTAtomParamsEx(allowParams: bool, allowBorrow: bool)
  choices("type atom", [
    {
      pSpecial("(")
      choices("type parameters", [
        {
          val iparams = pSepBy("type params", {pParameter(allowBorrow)}, pComma)
          pSpecial(")")
          val (params, pinfos) = iparams.unzip
          Left((params, pinfos))
        },
        {
          val cs = pmany1("tuple commas", pComma)
          pSpecial(")")
          val tp = pTypeApp(typeTuple(cs.length + 1))
          Right(tp)
        }
      ])
    },
    {val tp1 = pTId(); val tp2 = pTypeApp(tp1); Right(tp2)},
    {Right(pTEffect())},
    {pSpecialOp("?"); Right(makeOptional(pTAtom()))}
  ])

fun pTypeApp(tp)
  val tps = maybe("type application", {angles({pSepBy("type params", pType, pComma)}).fst}).default([])
  pSynonym(tp, tps)

fun pSynonym(tp, tps): <ast,eenv,comp-flags,synonyms> ktype
  val res = maybe("Env")
    pSpecialOp("==")
    val rank = maybe("synonym rank", {pInteger().fst}).default(0)
    val body = pType()
    match tp
      TCon(TypeCon(name, kind)) ->
        match synonymsLookup(name)
          Just(info as SynInfo(_, kind', _, _, rank')) ->
            TSyn(TypeSyn(name, kind', rank', Just(info)), tps, body)
          _ -> TSyn(TypeSyn(name, kind, rank, Nothing), tps, body)
      TSyn | tps.is-empty -> tp
      _ -> fail("illegal type alias expression " ++ tp.show)
  match res
    Just(t) -> t
    Nothing -> envTypeApp(tp, tps)

fun pTEffect()
  with try("typeEffect")
  pLangle()
  val labels = pSepBy("effect type", pTLabel, pComma)
  val ext = pTExtend()
  pRangle()
  labels.foldr(ext, shallowEffectExtend)

fun pTExtend(): <ast,eenv,comp-flags,synonyms> ktype
  maybe("effect extend", {pBar(); pTAtom()}).default(effectEmpty)

fun pTLabel()
  pTypeApp(pTAtom())

fun pTId(): <ast,eenv,comp-flags,synonyms> ktype
  val (name, _) = choices("type id", [pQVarId, pQIdOp, pWildcard])
  val kind = maybe("type kind", pKindAnnotFull).default(kindStar)
  envType(name, kind)

fun pKind()
  choices("kind", [
    {val params = parensCommas(pKind).fst; pKeyword("->"); val res = pKind(); params.foldr(res, kind-fun)},
    {val k = pKatom(); choices("kind arrow", [{pKeyword("->"); val res = pKind(); kind-fun(k, res)}, {k}])}
  ])

fun pKatom()
  choices("kind", [
    {parens(pKind).fst},
    {pSpecialConId("V"); kindStar},
    {pSpecialConId("X"); kindLabel},
    {pSpecialConId("E"); kindEffect},
    {pSpecialConId("H"); kindHeap},
    {pSpecialConId("S"); kindScope},
    {pSpecialConId("HX"); kindHandled},
    {pSpecialConId("HX1"); kindHandled1},
    {pSpecialConId("P"); kindPred}
  ])


effect eenv
  fun envExtend(name: name, kind: kind): ()
  fun envType(name: name, kind: kind): ktype
  fun envQualify(name: name): name
  fun envExtendSynonym(synInfo: synInfo): ()
  fun envTypeApp(tp: ktype, args: list<ktype>): ktype
  fun envExtendLocal(name: name, tp: ktype): ()
  fun envLookupLocal(name: name): ktype
  fun envLookupCon(name: name): nameInfo
  fun envLookupVar(name: name): expr
  val modname : name
  fun getEnv(): envv;
  fun setEnv(env: envv): ()

struct envv
  bound: linearMap<name, typeVar>
  imports: importmap
  unique: int
  gamma: gamma
  locals: linearMap<name, ktype>
  synonyms: name-map<synInfo>;

fun withEnvInitial(modName: name, imports0, f: () -> <eenv,ast,comp-flags,synonyms> a): <comp-flags,ast> a
  with withSynonyms(synonyms/empty)
  var bound := LinearMap([])
  var imports := imports0
  var unique := 1000
  var gamma := assumption/empty
  var locals := LinearMap([])
  fun qualify(n: name)
    if n.isQualified then
      match imports.importsExpand(n)
        Right((qname, _)) -> qname
        Left(amb) -> 
          trace("core/parse qualify: unable to expand name: " ++ n.show ++ ": " ++ amb.show-list(show))
          n
    else name/qualify(modName, n)
  with handler
    fun getEnv()
      Envv(bound, imports, unique, gamma, locals, getSynonyms())
    fun setEnv(e)
      val Envv(b, i, u, g, l, s) = e
      bound := b
      imports := i
      unique := u
      gamma := g
      locals := l
      setSynonyms(s)
    val modname = modName
    fun envExtend(n, k)
      val id = newId(unique)
      unique := unique + 1
      val tv = TypeVar(id, k, Bound)
      bound := bound.add(n, tv)
    fun envExtendLocal(n, k)
      unique := unique + 1
      locals := locals.set(n, k)
    fun envType(n, k)
      match bound.maybeGet(n)
        Just(tv) -> TVar(tv)
        Nothing ->
          val qname = qualify(n)
          match synonymsLookup(qname)
            Just(info as SynInfo(name, kind, params, tp, rank)) | params.is-empty ->
              TSyn(TypeSyn(name, kind, rank, Just(info)), [], tp)
            _ -> TCon(TypeCon(qname, k))
    fun envQualify(n)
      qualify(n)
    fun envExtendSynonym(synInfo)
      synonymsExtend(synInfo.name, synInfo)
    fun envTypeApp(tp, tps)
      match tp
        TCon(TypeCon(name0, _)) ->
          match synonymsLookup(name0)
            Just(synInfo as SynInfo(name, kind, params, syntp, rank)) | params.length == tps.length ->
              TSyn(TypeSyn(name, kind, rank, Just(synInfo)), tps, subNew(params.zip(tps)) |-> syntp)
            _ -> typeApp(tp, tps)
        _ -> typeApp(tp, tps)
    fun envLookupLocal(n)
      match locals.maybeGet(n)
        Just(tp) -> tp
        Nothing -> fail("core/parse unbound local: " ++ n.show)
    fun envLookupCon(n)
      match gamma.gammaLookupExactCon(n)
        [c as InfoCon] -> c
        res -> fail("unknown constructor " ++ n.show ++ ": " ++ res.show-list(show))
    fun envLookupVar(n)
      match gamma.gammaLookupCanonical(n)
        [fnct as InfoFun] -> fnct.coreExpr(n)
        [v as InfoVal] -> v.coreExpr(n)
        [ex as assumption/InfoExternal] -> ex.coreExpr(n)
        [] | n == nameFieldAddrOf -> 
          val a = TypeVar(0, kindStar, Bound)
          val fType = TForAll([a], [], TFun([(nameNil, TVar(a)), (nameNil, typeString), (nameNil, typeString)], typeTotal, TApp(typeFieldAddr, [TVar(a)])))
          Var(TName(nameFieldAddrOf, fType), compiler/core/core/InfoExternal([]))
        res -> fail("unknown identifier: " ++ n.showPlain ++ ": " ++ res.show-list(show)) 
  f()
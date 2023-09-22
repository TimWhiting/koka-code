import std/os/path
import compiler/common/parse
import compiler/syntax/lexeme
import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/common/name-prim
import compiler/kind/kind
import compiler/kind/synonyms
import compiler/kind/importmap
import compiler/type/type
import compiler/type/assumption
import core

fun parseCore(fname: path)
  lexParse(False, fn(lexes) lexes.allowDotIds.requalify, pProgram, fname.string, read-text-file(fname))

fun requalify(lexes: list<lexeme>): div list<lexeme>
  match lexes
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexId(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(mod.showPlain), name))), lexx))
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexIdOp(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(mod.showPlain), name))), lexx))
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexOp(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(mod.showPlain), name))), lexx))
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexCons(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexCons(qualify(newName(mod.showPlain), name))), lexx))
    Cons(lex, lexx)
      -> Cons(lex, requalify(lexx))
    [] -> []

fun allowDotIds(lexes: list<lexeme>): div list<lexeme>
  match lexes
    // Identifier
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexId(name)), lexx)) -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(prepend(".", name))), lexx))
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexWildCard(name)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2),  LexWildCard (".".prepend(name))), lexx))
    Cons(Lexeme(r1, LexId(name)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId (postpend("." ++ i.show, name))), lexx))
    // operator
    Cons(Lexeme(r1, LexKeyword(".")),Cons(Lexeme(r2, LexOp(name)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(".".prepend(name))), lexx))
    Cons(Lexeme(r1, LexOp(name)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId(postpend("." ++ i.show, name))), lexx))

    // constructor
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexCons(name)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexCons(".".prepend(name))), lexx))
    Cons(Lexeme(r1, LexCons(name)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexCons(postpend("." ++ i.show, name))), lexx))

    // (-.4), (++.2)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(name)), Cons(Lexeme(_,LexInt(i)),Cons(Lexeme(r5,LexSpecial(")")), lexx)))) // | last (nameId name) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(postpend(i.show, name))), lexx))
    // (/.4)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(name)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r5, LexSpecial(")")), lexx))))) // | last (nameId name) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(postpend("." ++ i.show, name))), lexx))
    // ([].1)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")),Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(_, LexKeyword(".")),Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r2, LexSpecial(")")), lexx))))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(postpend("." ++ i.show, "[]".newName))), lexx))
    // ([])
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")), Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(r2, LexSpecial(")")), lexx))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId("[]".newName)), lexx))
    Cons(l, lx) -> Cons(l, allowDotIds(lx))
    Nil -> Nil

fun pProgram()
  pmany("semis", pSemicolon)
  val (prog, env, inlines) = pModule()
  peof()
  (prog, pInlines(prog, source, env, inlines))

fun pModule()
  val (rng, doc) = pDocKeyword("module")
  pKeyword("interface")
  val (name, _) = pModulePath()
  pmany("semis", pSemicolon)
  braced
    val (imps, impAliases) = semis("", pImportDecl).unzip
    ()

fun pImportDecl(): <ast> (compiler/core/core/kimport, (name, name))
  unimplemented()

fun pTResult(params)
  ()

fun pTAtom()
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
      choices("", [
        {
          val iparams = pSepBy("", {pParameter(allowBorrow)}, pComma)
          pSpecial(")")
          val (params, pinfos) = iparams.unzip
          Left((params, pinfos))
        },
        {
          val cs = pmany1("", pComma)
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
  val tps = maybe("", angles({pSepBy("", pType, pComma)})).default([])
  pSynonym(tp, tps)

fun pSynonym(tp, tps)
  val res = maybe("Env")
    pSpecialOp("==")
    val (rank, _) = maybe("", pInteger).default((0, rangeNull))
    val body = pType()
    match tp
      TCon(TypeCon(name, kind)) ->
        match synonymsLookup(name)
          Just(info as SynInfo(synname, kind, params, syntp, rank)) ->
            TSyn(TypeSyn(name, kind, rank, Just(info)), tps, body)
          _ -> TSyn(TypeSyn(name, kind, rank, Nothing), tps, body)
      TSyn | tps.is-empty -> tp
      _ -> fail("illegal type alias expression " ++ tp.show)
  match res
    Just(t) -> t
    Nothing -> envTypeApp(tp, tps)

fun pTEffect()
  pLangle()
  val labels = pSepBy("", pTLabel, pComma)
  val ext = pTExtend()
  pRangle()
  labels.foldr(ext, shallowEffectExtend)

fun pTExtend()
  maybe("", {pBar(); pTAtom()}).default(effectEmpty)

fun pTLabel()
  pTypeApp(pTAtom())

fun pTId()
  val (name, _) = choices("", [pQVarId, pQIdOp, pWildcard])
  val kind = maybe("", pKindAnnotFull).default(kindStar)
  envType(name, kind)

fun pKind()
  choices("kind", [
    {val params = parensCommas("", pKind); pKeyword("->"); val res = pKind(); params.foldr(res, kindFun)},
    {val k = pKatom(); choices("", [{pKeyword("->"); val res = pKind(); kindFun(k, res)}, {k}])}
  ])

fun pKatom()
  choices("kind", [
    {parens(pKind)},
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
  fun extendLocal(name: name, tp: ktype): ()
  fun envLookupLocal(name: name): ktype
  fun envLookupCon(name: name): nameInfo
  fun envLookupVar(name: name): expr

fun withEnvInitial(modName, imports, f)
  with withSynonyms(synonyms/empty)
  var bound := linearMap([], fn(x: name, y: name) x == y, fn(x: typeVar, y: typeVar) x == y, fn(x) x.show, fn(x) x.show)
  var imports := imports
  var unique := 1000
  var gamma := assumption/empty
  var locals := linearMap([], fn(x: name, y: name) x == y, fn(x: ktype, y: ktype) x == y, fn(x) x.show, fn(x) x.show)
  fun qualify(n: name)
    if n.isQualified then
      match imports.importsExpand(n)
        Right(qname, _) -> qname
        Left(amb) -> 
          trace("core/parse qualify: unable to expand name: " ++ n.show ++ ": " ++ amb.show)
          n
    else qualify(mname, n)
  with handler
    fun envExtend(n, k)
      val id = newId(unique)
      unique := unique + 1
      val tv = TypeVar(id, k, Bound)
      bound := bound.insert(n, tv)
    fun envType(n, k)
      match bound.maybeGet(n)
        Just(tv) -> tv
        Nothing ->
          val qname = qualify(n)
          match synonyms.lookup(qname)
            Just(info as SynInfo(name, kind, params, tp, rank)) | params.is-empty ->
              TSyn(TypeSyn(name, kind, rank, Just(info), [], tp))
            _ -> TCon(TypeCon(qname, k))
    fun envQualify(n)
      qualify(n)
    fun envExtendSynonym(synInfo)
      synonymsExtend(synInfo)
    fun envTypeApp(tp, args)
      match tp
        TCon(TypeCon(name0, kind0)) ->
          match synonymsLookup(name0)
            Just(synInfo as SynInfo(name, kind, params, syntp, rank)) | params.length == tps.length ->
              TSyn(TypeSyn(name, kind, rank, Just(synInfo)), tps, subNew(params.zip(tps) |-> syntp))
            _ -> typeApp(tp, tps)
        _ -> typeApp(tp, tps)
    fun extendLocal(n, tp)
      unique := unique + 1
      locals := locals.set(n, tp)
    fun envLookupLocal(n)
      match locals.maybeGet(n)
        Just(tp) -> tp
        Nothing -> error("core/parse unbound local: " ++ n.show)
    fun envLookupCon(n)
      match g.gammaLookupExactCon(n)
        [c as InfoCon] -> c
        res -> fail("unkown constructor " ++ n.show ++ ": " ++ res.show)
    fun envLookupVar(n)
      match g.gammaLookupCanonical(n)
        [f as InfoFun] -> f.coreExpr(n)
        [v as InfoVal] -> v.coreExpr(n)
        [ex as assumption/InfoExternal] -> ex.coreExpr(n)
        [] | name == nameFieldAddrOf -> 
          val a = TypeVar(0, kindStar, Bound)
          val fType = TForAll([a], [], TFun([(nameNil, TVar(a)), (nameNil, typeString), (nameNil, typeString)], typeTotal, TApp(typeFieldAddr, [TVar(a)])))
          Var(TName(nameFieldAddrOf, fType), compiler/core/core/InfoExternal([]))
        res -> fail("unknown identifier: " ++ n.showPlain ++ ": " ++ res.show) 
  f()
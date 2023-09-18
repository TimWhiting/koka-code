import std/text/parse
import std/os/path
import std/os/file
import compiler/syntax/lexer2
import compiler/syntax/lexeme
import compiler/syntax/layout
import compiler/syntax/syntax
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/syntax/promote

effect astError
  final ctl astError(e: string, r: range): a

effect astParse
  val sourceInfo: source
  fun addWarning(w: string, r: range): ()
  fun ppeek(): maybe<lexeme>
  fun commit(): ()
  fun reset(): ()
  fun pdelimit(msg: string): ()
  fun pnext(): maybe<lexeme>
  fun peof(): ()
  fun tookInput(): bool
  fun ptrace(s: string): ()

fun peek(): ast lexeme
  val p = ppeek()
  match p
    Just(l) -> l
    Nothing -> astError("unexpected end of file", rangeNull)

fun next(): ast lexeme
  val p = pnext()
  match p
    Just(l) -> l
    Nothing -> astError("unexpected end of file", rangeNull)

alias ast = <astParse, astError, pure>

fun parseProgramFromFile(semiInsert: bool, fname: path)
  val r = read-text-file(fname)
  parseProgramFromString(semiInsert, r, fname)

fun parseProgramFromString(semiInsert: bool, input: string, fname: path)
  lexParse(semiInsert, fn(x) x, parseProgram, fname.string, input)

fun lexParse(insSemi: bool, preprocess: list<lexeme> -> list<lexeme>, p: () -> <console,ast|e> a, sourceName: string, input: string): <console,astError,pure|e> a
  val src = Source(sourceName, input)
  val lexes = lex(src, 0, input)
  var lexemes := preprocess(layout(insSemi, lexes))
  var history := Cons((ctx _, "top", 0), Nil)
  val debug = True
  with override
    final ctl astError(e: string, r: range)
      astError("Got error: " ++ e ++ "\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n"), r)
  with handler
    val sourceInfo = src
    fun addWarning(w: string, r: range)
      ()
    fun pnext()
      match lexemes
        Cons(l, rst) ->
          lexemes := rst
          match history
            Cons((h, msg, i), tl) ->
              history := Cons((h ++ ctx Cons(l, _), msg, i + 1), tl)
            Nil -> 
              astError("unexpected top of context", rangeNull)
          Just(l)
        Nil -> Nothing
    fun reset()
      match history
        Cons((h, str, _), rst) -> 
          lexemes := h ++. lexemes
          history := rst
          if debug then
            trace("Resetting " ++ str ++ "\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ " at " ++ lexemes.head.map(show).default("eof"))
        Nil ->
          astError("mismatched reset", rangeNull)
    fun pdelimit(msg)
      history := Cons((ctx _, msg, 0), history)
    fun commit()
      history := history.tail
    fun ppeek()
      match lexemes
        Cons(l, _) -> Just(l)
        Nil -> Nothing
    fun peof()
      trace("Parsing eof\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ "\n\nHad leftovers: " ++ lexemes.map(fn(x) x.show).join("\n"))
      match lexemes
        Cons(l, _) ->
          astError("peof expected end of file", l.range)
        Nil ->
          ()
    fun tookInput()
      match history
        Cons((_, _, i), _) -> 
          i != 0
        Nil ->
          False
    fun ptrace(s: string)
      trace(s ++ "\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ "\n\n Next tokens: " ++ lexemes.head.map(show).default("eof"))
  mask<local>{p()}

fun interactive(f: () -> <ast> a): <ast> a
  val x = f()
  pmany("semicolons", pSemicolon)
  x

fun pmany(kind: string, l: () -> <ast> a): <ast> list<a>
  match maybe("many " ++ kind, l)
    Just(r) -> Cons(r, pmany(kind, l))
    Nothing -> Nil

fun pmany1(kind: string, l: () -> <ast> a): <ast> list<a>
  match maybe("many " ++ kind, l)
    Just(r) -> Cons(r, pmany(kind, l))
    Nothing -> astError("at least 1 of " ++ kind, peek().range)

fun pmanyend(kind: string, l: () -> <ast> a, p: () -> <ast> b): <ast> list<a>
  match maybe("many " ++ kind, l)
    Just(r) -> 
      match maybe("sep " ++ kind, p)
        Just(_) -> Cons(r, pmanyend(kind, l, p))
        Nothing -> Cons(r, Nil)
    Nothing -> Nil

fun token(msg: string, f: (lexeme) -> <ast|e> maybe<a>): <ast|e> a
  val t = peek()
  match f(t) 
    Just(a) -> 
      ptrace("Consuming " ++ t.show)
      next() 
      a
    Nothing ->
      astError("expecting " ++ msg, peek().range)

// Version of maybe that does backtrack
fun maybe(str: string, p: () -> <ast> a): <ast> maybe<a>
  with override
    return(r) 
      Just(r)
    final ctl astError(e, r) 
      reset()
      Nothing
  pdelimit(str)
  val x = p()
  commit()
  x

fun maybeList(p: () -> <ast> list<a>): <ast> list<a>
  match maybe("list", p)
    Just(r) -> r
    Nothing -> []

// Version of maybe that doesn't backtrack
fun maybenb(str: string, p: () -> <ast> a): <ast> maybe<a>
  with override
    return(r) 
      Just(r)
    final ctl astError(e, r) 
      Nothing
  p()

fun choicesnb(str: string, ps: list<() -> <ast> a>): <ast> a
  fun find(ps': list<() -> <ast> a>): <ast> a
    match ps'
      Cons(p, rst) -> 
        match maybenb(str, p)
          Just(r) -> r
          Nothing -> 
            if tookInput() then
              astError("expected " ++ str, peek().range)
            else
              find(rst)
      Nil -> astError("expected " ++ str, peek().range)
  with override
    final ctl astError(e, r) 
      reset()
      astError(e, r)
  pdelimit(str)
  val x = find(ps)
  commit()
  x

fun choices(str: string, ps: list<() -> <ast> a>): <ast> a
  match ps.find-maybe(fn(p) maybe(str, p)) // TODO Capture error from below for better error message expected one of...
    Just(r) -> r
    Nothing -> astError("expected " ++ str, peek().range)

fun pSemicolon(): <ast> lexeme
  token("semicolon") fn(x) 
    if x.is-semicolon then Just(x) else Nothing

fun makeParseError(r: range, e: string)
  astError("invalid syntax" ++ e.list.drop-while(fn(x) x != ':').string, r)

fun parseProgram()
  pmany("semicolons", pSemicolon)
  val p = pModule()
  peof()
  p

fun pModule()
  val res = maybe("module name")
    val vis = pVisibility().fst
    val doc = pDocKeyword("module", []).snd
    val (name, rng) = pModulePath() 
    pBody(vis, name, rng, doc)
  match res
    Just(r) -> r
    Nothing -> pBody(Public, sourceInfo.name.path.basename.pathToModuleName, rangeNull, "")

fun pBody(vis: visibility, name: name, rng: range, doc: string): <ast> userProgram
  pmany("semicolons", pSemicolon)
  val (imports, fixDefss, topDefss) = braced
    val imps = semis("imports", pImportDecl)
    val fixs = semis("fixities", pFixityDecl)
    val tdefs = semis("topDefs", fn() pTopDef(vis))
    (imps, fixs, tdefs)
  pmany("semicolons", pSemicolon)
  val (defs, typeDefs, externals) = splitTopDefs(topDefss.concat)
  val prelude = if name.show.starts-with("std/core").is-just then [] else [Kimport(nameSystemCore, nameSystemCore, rangeNull, Private)]
  Program(sourceInfo, name, rng, [TypeDefRec(typeDefs)], [DefRec(defs)], prelude ++ imports, externals, fixDefss.concat, doc)

fun braced(p)
  val v = maybe("braced") 
    pLcurly()
    pmany("semicolons", pSemicolon)
    val x = p()
    pmany("semicolons", pSemicolon)
    pRcurly()
    x
  match v
    Just(v') -> v'
    Nothing -> p()

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
  val _ = pKeyword("import", [])
  val (asname, name, rng) = pImportAlias()
  Kimport(asname, name, Range(vrng.start, rng.end), vis)

fun pImportAlias()
  val (name1, rng1) = pModulePath()
  val r = maybe("import alias")
    val _ = pKeyword("=", [])
    pModulePath()
  match r
    Just((name2, rng2)) -> (name1, name2, rng2)
    Nothing -> (name1, name1, rng1)

fun pVisibility(vis=Private)
  choices("visibility", [{
    val x = pKeyword("pub", ["public"])
    (Public, x.range)
  },
  {
    val x = pKeyword("private", [])
    addWarning("using private is deprecated, only use pub to make declarations public", x.range)
    (Private, x.range)
  },{(vis, rangeNull)}])

fun pInline()
  choices("inline", [{
    val _ = pSpecialId("inline")
    InlineAlways
  }, {
    val _ = pSpecialId("noinline")
    InlineNever
  }, {InlineAuto}])

fun warnDeprecated(o: string, n: string, rng: range): <ast> ()
  addWarning("using deprecated " ++ o ++ ", use " ++ n ++ " instead", rng)

fun typeFromPars(rng:range, pars: list<valueBinder<userType, maybe<userExpr>>>, teff: userType, tres: userType): div userType
  promoteType(TpFun(pars.map(fn(p) (p.name, p.binderType)), teff, tres, rng))

fun genArgs(pars: list<valueBinder<userType, maybe<userExpr>>>): list<(maybe<userExpr>, userExpr)>
  pars.map(fn(p) (Nothing, Var(p.name, False, p.range.before)))

fun genParArgs(tp)
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
  pars.map-indexed(fn(i, p) p.genParArg(i))

fun genParArg((name:name, _:userType), idx: int)
  val fullName = if name == nameNil then newHiddenName("arg" ++ idx.show) else name
  val rng = rangeNull
  (ValueBinder(fullName, Nothing, Nothing, rng, rng), Nothing, Var(fullName, False, rng))


fun pExternDecl(dvis: visibility): <ast> list<topDef>
  choices("externDecl", [{
    val krng = pDocKeyword("extern", []).fst
    val _ = choices("import", [
      {pKeyword("import", []); ()},
      {
        pSpecialId("include"); 
        warnDeprecated("include", "import", krng); 
      }])
    [DefExtern(externalImport(krng))]
  }, {
    val (vis,vrng) = pVisibility(dvis)
    val inl = pInline()
    val fip = pFip()
    val (krng,doc) = pDocKeyword("extern",[])
    val (name, nameRng) = pFunId()
    val (pars, pinfos, args, tp, annotates) = choices("extern type", [
      {
        pKeyword(":", [])
        val tp = pType()
        val (pars, args) = genParArgs(promoteType(tp))
        (pars, [], args, tp, fn(body) Ann(body, tp, tp.range))
      },
      {
        val tpPars = pTypeParams()
        val (pars, pinfos, parRng) = pDeclParams(True, inl != InlineAlways)
        val (teff, tres) = pAnnotResult()
        val tp = typeFromPars(nameRng, pars, teff, tres)
        (pars.map(fn(ValueBinder(name, tp, expr, rng1, rng2)) ValueBinder(name, Just(tp), expr, rng1, rng2)), pinfos, genArgs(pars), tp, fn(body) promote([], tpars, [], Just(Just((teff, tres))), body))
      }
    ])
    val (exprs, rng) = pExternalBody()
    val fullRng = Range(krng.start, rng.end)
    if (inl == InlineAlways) then [DefExtern(External(name, tp, pinfos, nameRng, fullRng, exprs, vis, fip, doc))]
    else
      val externName = newHiddenExternalName(name)
      val ext = External(externName, tp, pinfos, nameRng.before, fullRng.before, exprs, Private, fip, doc)
      val body = annotate(Lam(pars, App(Var(externName, False, rangeNull), args, fullRng), fullRng))
      val binder = ValueBinder(name, (), body, nameRng, fullRng)
      val extfun = Def(binder, fullRng, vis, defFunEx(pinfos, fip), InlineNever, doc)
      [DefExtern(ext, extfun)]
  }
  ])
  

fun externalImport(r: range): <ast> external
  unimplemented()
 
fun pFixityDecl(): <ast> list<fixDef>
  unimplemented()

fun pAliasDecl(vis: visibility)
  unimplemented()

fun pTypeDecl(vis: visibility)
  unimplemented()

fun pEffectDecl(vis: visibility)
  unimplemented()


fun pDeclParams(allowBorrow: bool, allowDefaults: bool)
  fun pParamBinder() 
    val pinfo = if allowBorrow then pParamInfo() else Own
    val (name, rng, tp) = pParamType()
    val (opt, drng) = if allowDefaults then pDefaultExpr() else (Nothing, rangeNull)
    ValueBinder(name, tp, opt, rng, combineRanges([rng, tp.range, drng]), pinfo)
  val (ipars, rng) = parensCommas(pParamBinder)
  val (pars, pinfos) = ipars.unzip
  (pars, pinfos, rng)

fun pParamInfo()
  choices("param info", [{
    pSpecialOp("^")
    Borrow
  }, {Own}])

fun pPureDecl(vis: visibility)
  unimplemented()


fun pFipAlloc()
  parens
    choices("alloc", [
      {
        val (i, _) = pInteger()
        AllocAtMost(i)
      },
      {
        val _ = pSpecialId("n")
        AllocFinitely
      },
      {
        AllocAtMost(0)
      }
    ])

fun pFip()
  val isTail = choices("tail", [{pSpecialId("tail"); True}, {False}])
  choices("fip", [{
    val rng = pSpecialId("fip")
    val (alloc, _) = pFipAlloc()
    if isTail then
      addWarning("fip function already implies 'tail'", rng)
    Fip(alloc)
    }, 
    {
    pSpecialId("fbip")
    val (alloc, _) = pFipAlloc()
    Fbip(alloc, isTail)
    }, 
    {NoFip(isTail)}])



fun pTypeParams()
  maybeList({angles(pTBinders).fst})

fun pTBinders()
  pSepBy("type binder", pTBinder, pComma)

fun pTBinder()
  val (id, rng) = pVarId()
  val kind = pKindAnnotation()
  return TypeBinder(id, kind, rng, rng)

fun pKindAnnotation()
  choices("kind", [{
    pSpecialId("::")
    pKind()
  },
  {KindNone}])

fun pKind()
  choices("kind", [
   {
    val (params, _) = parensCommas(pKind)
    pKeyword("->", [])
    val res = pKind()
    params.foldr(res, fn(a, acc) KindArrow(a, acc))
   },
   {
    val k = pKindAtom()
    choices("kind", [{
      pKeyword("->", [])
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

fun pFunId()
  choicesnb("function id", [
    {pIdentifier()},
    {
      val rng1 = pSpecialId("[")
      val rng2 = pSpecialId("]")
      (nameIndex, Range(rng1.start, rng2.end))
    },
    {
      val (s, rng) = pStringLit()
      (newName(s), rng)
    }
    ])



fun semis(kind, p)
  pmanyend(kind, p, pSemi1)

val pSepBy = pmanyend

fun pSemi1()
  pmany1("semicolons", pSemicolon)

fun parens(p)
  val l = pLparen()
  val x = p()
  val r = pRparen()
  (x, Range(l.start, r.end))

fun pComma()
  pSpecial(",")

fun angles(p)
  val l = pLangle()
  val x = p()
  val r = pRangle()
  (x, Range(l.start, r.end))

fun parensCommas(p)
  parens
    pSepBy("comma", p, pComma)

fun parseRange(msg: string, f: (lexeme) -> <ast|e> bool): <ast|e> range
  token(msg, fn(x) if f(x) then Just(x) else Nothing).range

fun pLcurly()
  parseRange("{", fn(x) x.lex.is-lcurly)

fun pRcurly()
  parseRange("}", fn(x) x.lex.is-rcurly)

fun pLparen()
  parseRange("(", fn(x) x.lex.is-lparen)

fun pRparen()
  parseRange(")", fn(x) x.lex.is-rparen)

fun pLangle()
  parseRange("(", fn(x) x.lex.is-langle)

fun pRangle()
  parseRange(")", fn(x) x.lex.is-rangle)

fun pIdentifier()
  ensureUnqualified("identifier", pQIdentifier)

fun pVarId()
  ensureUnqualified("variable id", pQVarId)

fun pModulePath(): <ast> (name, range)
  token("module path") fn(x)
    match x 
      Lexeme(rng, LexId(id)) -> 
        Just((id.showPlain.newName, rng))
      _ -> Nothing

fun pQIdentifier()
  choices("qidentifier", [pQVarId, pQIdOp])

fun ensureUnqualified(str, p)
  val (n, r) = p()
  if n.isQualified then 
    astError("expected unqualified " ++ str, r)
  else
    (n, r)

fun pQVarId()
  token("variable id") fn(a)
    match a
      Lexeme(rng, LexId(id)) -> 
        Just((id.showPlain.newName, rng))
      _ -> Nothing

fun pQIdOp()
  token("operator id") fn(a)
    match a
      Lexeme(rng, LexIdOp(id)) -> 
        Just((id, rng))
      _ -> Nothing

fun pQConId()
  token("constructor id") fn(a)
    match a
      Lexeme(rng, LexCons(id)) -> 
        Just((id, rng))
      _ -> Nothing

fun pStringLit()
  token("string literal") fn(x) 
    match x
      Lexeme(rng, LexString(s)) -> Just((s, rng))
      _ -> Nothing

fun pSpecialId(s: string)
  token("special id " ++ s) fn(x)
    match x.lex
      LexId(id) | id.showPlain == s -> Just(x.range)
      _ -> Nothing

fun pSpecial(s)
  token(s) fn(x)
    match x.lex
      LexSpecial(s') | s == s' -> Just(x.range)
      _ -> Nothing

fun pSpecialOp(s)
  token(s) fn(x)
    match x.lex
      LexOp(s') | s == s'.showPlain -> Just(x.range)
      _ -> Nothing

fun pSpecialConId(s)
  token(s) fn(x)
    match x.lex
      LexCons(s') | s == s'.showPlain -> Just(x.range)
      _ -> Nothing

fun pKeyword(s: string, alternates: list<string>): <ast> lexeme
  token("keyword " ++ s) fn(x)
    match x.lex
      LexKeyword(s', _) | s == s' -> Just(x)
      LexKeyword(s', _) | alternates.any(fn(v) v == s') -> 
        addWarning("using deprecated keyword " ++ s' ++ ", use " ++ s ++ " instead", x.range)
        Just(x)
      _ -> Nothing

fun pDocKeyword(s: string, alternates: list<string>): <ast> (range, string)
  match pKeyword(s, alternates)
    Lexeme(rng, LexKeyword(_, doc)) -> (rng, doc)
    _ -> astError("expected " ++ s, rangeNull)

fun pInteger()
  token("integer") fn(l)
    match l
      Lexeme(_, LexInt(i)) -> Just((i, l))
      _ -> Nothing


fun unimplemented()
  astError("unimplemented", peek().range)
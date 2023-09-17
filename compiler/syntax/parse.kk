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
  var lexemes := preprocess(layout(insSemi, lex(src, 0, input)))
  var history := Cons((ctx _, "top"), Nil)
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
            Cons((h, msg), tl) ->
              history := Cons((h ++ ctx Cons(l, _), msg), tl)
            Nil -> 
              astError("unexpected top of context", rangeNull)
          Just(l)
        Nil -> Nothing
    fun reset()
      match history
        Cons((h, _), rst) -> 
          lexemes := h ++. lexemes
          history := rst
        Nil ->
          astError("mismatched reset", rangeNull)
    fun pdelimit(msg)
      history := Cons((ctx _, msg), history)
    fun commit()
      history := history.tail
    fun ppeek()
      match lexemes
        Cons(l, _) -> Just(l)
        Nil -> Nothing
    fun peof()
      match lexemes
        Cons(l, _) ->
          astError("peof expected end of file", l.range)
        Nil ->
          ()
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

fun token(msg: string, f: (lexeme) -> <ast|e> bool): <ast|e> lexeme
  if f(peek()) then next() else astError("expecting " ++ msg, peek().range)

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

// Version of maybe that doesn't backtrack
fun maybenb(str: string, p: () -> <ast> a): <ast> maybe<a>
  with override
    return(r) 
      Just(r)
    final ctl astError(e, r) 
      Nothing
  p()

fun choicesnb(str: string, ps: list<() -> <ast> a>): <ast> a
  match ps.find-maybe(fn(p) maybenb(str, p))
    Just(r) -> r
    Nothing -> astError("expected " ++ str, peek().range)

fun choices(str: string, ps: list<() -> <ast> a>): <ast> a
  match ps.find-maybe(fn(p) maybe(str, p))
    Just(r) -> r
    Nothing -> astError("expected " ++ str, peek().range)

fun pSemicolon()
  val l = next()
  if l.is-semicolon then l else astError("expected semicolon", l.range)

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
    val doc = pDocKeyword("module").snd
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
  val _ = pKeyword("import")
  val (asname, name, rng) = pImportAlias()
  trace("importing " ++ name.show ++ " as " ++ asname.show)
  Kimport(asname, name, Range(vrng.start, rng.end), vis)

fun pImportAlias()
  val (name1, rng1) = pModulePath()
  val r = maybe("import alias")
    val _ = pKeyword("=")
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
    val x = pKeyword("private")
    addWarning("using private is deprecated, only use pub to make declarations public", x.range)
    (Private, x.range)
  },{(vis, rangeNull)}])

fun pInline()
  choices("inline", [{
    val _ = specialId("inline")
    InlineAlways
  }, {
    val _ = specialId("noinline")
    InlineNever
  }, {InlineAuto}])

fun pExternDecl(vis: visibility)
  unimplemented()

fun pFixityDecl(): <ast> list<fixDef>
  unimplemented()

fun pAliasDecl(vis: visibility)
  unimplemented()

fun pTypeDecl(vis: visibility)
  unimplemented()

fun pEffectDecl(vis: visibility)
  unimplemented()

fun pPureDecl(vis: visibility)
  unimplemented()

fun semis(kind, p)
  pmanyend(kind, p, pSemi1)

fun pSemi1()
  pmany1("semicolons", pSemicolon)

fun parseRange(msg: string, f: (lexeme) -> <ast|e> bool): <ast|e> range
  token(msg, f).range

fun pLcurly()
  parseRange("expected {", fn(x) x.lex.is-lcurly)

fun pRcurly()
  parseRange("expected }", fn(x) x.lex.is-rcurly)

fun pModulePath()
  val x = token("module path", fn(x) x.lex.is-lexId)
  match x 
    Lexeme(rng, LexId(id)) -> 
      (id.showPlain.newName, rng)
    _ -> astError("expected module path", rangeNull)

fun specialId(s: string)
  val x = token("special id " ++ s) fn(x)
    match x.lex
      LexId(id) | id.showPlain == s -> True
      _ -> False
  x.range

fun pKeyword(s: string, alternates: list<string> = []): <ast> lexeme
  token("keyword " ++ s) fn(x)
    match x.lex
      LexKeyword(s', _) | s == s' -> True
      LexKeyword(s', _) | alternates.any(fn(v) v == s') -> 
        addWarning("using deprecated keyword " ++ s' ++ ", use " ++ s ++ " instead", x.range)
        True
      _ -> False

fun pDocKeyword(s: string, alternates: list<string> = []): <ast> (range, string)
  match pKeyword(s, alternates)
    Lexeme(rng, LexKeyword(_, doc)) -> (rng, doc)
    _ -> astError("expected " ++ s, rangeNull)

fun unimplemented()
  astError("unimplemented", peek().range)
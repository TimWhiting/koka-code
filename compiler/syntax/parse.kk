import std/text/parse
import std/os/path
import std/os/file
import compiler/syntax/lexer2
import compiler/syntax/lexeme
import compiler/syntax/layout
import compiler/syntax/syntax
import compiler/common/syntax
import compiler/common/name
import compiler/common/range

effect astError
  final ctl astError(e: string, r: range): a

effect astParse
  val sourceInfo: source
  fun addWarning(w: string, r: range): ()
  fun ppeek(): maybe<lexeme>
  fun commit(): ()
  fun reset(): ()
  fun delimit(msg: string): ()
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
    fun delimit(msg)
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
  val r = maybe("many " ++ kind, l)
  match r
    Just(r) -> Cons(r, pmany(kind, l))
    Nothing -> Nil

fun maybe(str: string, p: () -> <ast> a): <ast> maybe<a>
  with override
    return(r) 
      Just(r)
    final ctl astError(e, r) 
      reset()
      Nothing
  delimit(str)
  val x = p()
  commit()
  x

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
    val vis = pVisibility().snd
    val doc = pDocKeyword("module").snd
    val (name, rng) = pModulePath() 
    pBody(vis, name, rng, doc)
  match res
    Just(r) -> r
    Nothing -> pBody(Public, sourceInfo.name.path.basename.pathToModuleName, rangeNull, "")

fun pBody(vis, name, rng, doc)
  ()

fun pModulePath()
  match next()
    Lexeme(rng, LexId(id)) -> 
      (id.showPlain.newName, rng)
    _ -> astError("expected module path", rangeNull)

fun pVisibility(vis=Private)
  match maybe("public", {pKeyword("pub", ["public"])})
    Just(t) -> (Public, t.range)
    Nothing ->
      match maybe("private", {pKeyword("private")})
        Just(t) -> 
          addWarning("using private is deprecated, only use pub to make declarations public", t.range)
          (Private, t.range)
        Nothing -> (vis, rangeNull)

fun pKeyword(s: string, alternates: list<string> = [])
  match next()
    l as Lexeme(lex=LexKeyword(s', _)) | s == s' || alternates.any(fn(x) x == s') ->
      l
    x -> 
      astError("expected keyword " ++ s ++ " or " ++ alternates.join(","), x.range)

fun pDocKeyword(s: string)
  match next()
    Lexeme(rng, LexKeyword(s', doc)) | s == s' -> 
      (rng, doc)
    _ -> astError("expected keyword " ++ s, rangeNull)

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

effect astParse
  val sourceInfo: source
  fun addWarning(w: string, r: range): ()
  final ctl astError(e: string, r: range): a
  fun currentInput(): list<lexeme>
  fun setCurrentInput(l: list<lexeme>): ()

fun parseProgramFromFile(semiInsert: bool, fname: path)
  val r = read-text-file(fname)
  parseProgramFromString(semiInsert, r, fname)

fun parseProgramFromString(semiInsert: bool, input: string, fname: path)
  lexParse(semiInsert, fn(x) x, parseProgram, fname.string, input)

fun lexParse(insSemi: bool, preprocess: list<lexeme> -> list<lexeme>, p: () -> <console,pure,astParse|e> a, sourceName: string, input: string): <console,pure|e> maybe<a>
  val src = Source(sourceName, input)
  val l = lex(src, 0, input)
  var lexemes := preprocess(layout(insSemi, l))
  with handler
    return(r) Just(r)
    val sourceInfo = src
    fun addWarning(w: string, r: range)
      ()
    final ctl astError(e, r)
      Nothing
    fun currentInput() lexemes
    fun setCurrentInput(lexs)
      lexemes := lexs
  mask<local>{p()}

fun interactive(f: () -> <pure,astParse> a): <pure,astParse> a
  val x = f()
  pmany(pSemicolon)
  x

fun pmany(l: () -> <pure,astParse> a): <pure,astParse> list<a>
  val r = maybe(l)
  match r
    Just(r) -> Cons(r, l.pmany)
    Nothing -> Nil

fun maybe(p: () -> <pure,astParse> a): <pure,astParse> maybe<a>
  with override
    return(r) Just(r)
    val sourceInfo = sourceInfo
    fun addWarning(w: string, r: range)
      addWarning(w, r)
    final ctl astError(e, r)
      Nothing
    fun currentInput() currentInput()
    fun setCurrentInput(lexs)
      setCurrentInput(lexs)
  p()

fun pSemicolon()
  match currentInput()
    Cons(l, tl) -> if l.is-semicolon then setCurrentInput(tl) else astError("expected semicolon", l.range)
    _ -> ()

fun makeParseError(r: range, e: string)
  astError("invalid syntax" ++ e.list.drop-while(fn(x) x != ':').string, r)

fun parseProgram()
  pmany(pSemicolon)
  val p = pModule()
  peof()
  p

fun ptry(p: () -> <pure,astParse> a): <pure,astParse> maybe<a>
  val curr-input = currentInput()
  val res = maybe(p)
  match res
    Just(r) -> Just(r)
    Nothing -> 
      setCurrentInput(curr-input);
      Nothing

fun pModule()
  val res = ptry
    val vis = pVisibility().snd
    val (_, doc) = pDocKeyword("module")
    val (name, rng) = pModulePath() 
    pBody(vis, name, rng, doc)
  match res
    Just(r) -> r
    Nothing -> pBody(Public, sourceInfo.name.path.basename.pathToModuleName, rangeNull, "")

fun pBody(vis, name, rng, doc)
  ()

fun pModulePath()
  match currentInput()
    Cons(Lexeme(rng, LexId(id)), tl) -> 
      setCurrentInput(tl)
      (id.showPlain.newName, rng)
    _ -> astError("expected module path", rangeNull)

fun pVisibility(vis=Private)
  match maybe({pKeyword("pub", ["public"])})
    Just(t) -> (Public, t.range)
    Nothing ->
      match maybe({pKeyword("private")})
        Just(t) -> 
          addWarning("using private is deprecated, only use pub to make declarations public", t.range)
          (Private, t.range)
        Nothing -> (vis, rangeNull)

fun pKeyword(s: string, alternates: list<string> = [])
  match currentInput()
    Cons(l, tl) ->
      if l.lex.is-lexKeyword then
        setCurrentInput(tl)
        l
      else
        astError("expected keyword " ++ s ++ " or " ++ alternates.join(","), l.range)
    _ -> astError("expected keyword " ++ s ++ " or " ++ alternates.join(","), rangeNull)

fun pDocKeyword(s: string)
  match currentInput()
    Cons(Lexeme(rng, LexKeyword(s', doc)), tl) | s == s' -> 
      setCurrentInput(tl)
      (rng, doc)
    _ -> astError("expected keyword " ++ s, rangeNull)

fun peof()
  match currentInput()
    Cons(l, _) -> astError("expected end of file", l.range)
    _ -> ()
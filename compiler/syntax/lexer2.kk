import compiler/syntax/lexeme
import compiler/syntax/lex2
import compiler/common/range
import std/os/file
import std/os/path

fun lex(source: string, pos: pos)
  var lexemes := ctx _
  var states := [0]
  var slices := []
  var current := source.slice
  var acc := current.truncate
  var char := ' '
  var prev := ' '
  var raw-delim := 0
  var start := pos
  var end := pos
  var atend := False
  with handler
    fun pop-state()
      match states
        Cons(s, rst) -> 
          states := rst
          s
        Nil -> throw("pop-state when no states")
    fun push-state(i)
      states := Cons(i, states)
    fun get-state()
      match states
        Cons(s) -> s
        Nil -> throw("get-state when no states")
    fun start-slice()
      slices := Cons("", slices)
    fun pop-slice()
      match slices
        Cons(s, rst) -> 
          slices := rst
          s
        Nil -> throw("pop-slice when no slices")
    fun next-char()
      match current.next()
        Just((c, s)) -> 
          prev := char
          char := c
          current := s
          acc := acc.extend(1)
          trace(acc.show)
          end := end.pos-move8(c)
          Just((c, s))
        Nothing -> 
          atend := True
          Nothing
    fun get-previous()
      prev
    fun extend-slice(f)
      match slices
        Cons(s, rst) -> 
          slices := Cons(s ++ f(acc).string, rst)
          acc := current.truncate
        Nil -> throw("extend-slice when no slices")
    fun get-slice()
      trace(acc.show)
      val res = if atend then acc else acc.extend(-1)
      acc := current.truncate
      res
    fun get-delim()
      raw-delim
    fun push-rawdelim()
      raw-delim := acc.count
      acc := current.truncate
    fun pop-rawdelim()
      raw-delim := 0
      acc := current.truncate
    fun emit(l)
      trace(l.show)
      lexemes := lexemes ++ ctx Cons(Lexeme(make-range(start, end), l), _)
      start := end
  alex-loop(current)
  lexemes ++. Nil

fun alex-loop(s)
  match alexScan(s, get-state())
    AlexToken(_, n, p) -> 
      p()
      alex-loop(s)
    AlexEOF -> ()
    AlexSkip -> throw("Skip")
    AlexError -> throw("Error")

fun lexer(path: string, line: int, input: string): <pure> list<lexeme>
  lexing(Source(path, input), line, input)

fun lexing(source: source, line: int, input: string)
  val init-pos = Pos(source, 0, 0, 1)
  with val alextrace = False
  lex(input, init-pos)

fun main()
  var done := False
  var s := read-text-file("compiler/syntax/simple.kk".path)
  val source = Source("compiler/syntax/simple.kk", s)
  lexing(source, 1, s).trace-show


import compiler/syntax/lexeme
import compiler/syntax/lex2
import compiler/common/range
import std/os/file
import std/os/path

fun lex(str: string, pos: pos)
  val src = pos.source
  var lexemes := []
  var slices := []
  var raw-delim := 0
  with handler
    fun start-chunked()
      slices := Cons("", slices)
    fun end-chunked()
      match slices
        Cons(s, rst) -> 
          slices := rst
          s
        Nil -> throw("end-chunked when no chunked input")
    fun add-chunk(f)
      match slices
        Cons(s, rst) -> 
          slices := Cons(s ++ f.string, rst)
        Nil -> throw("add-chunk when no chunked input")
    fun get-rawdelim()
      raw-delim
    fun set-rawdelim(i)
      raw-delim := i
    fun do-emit(l, lstart, lend)
      val Alex-pos(off, line, col) = lstart
      val Alex-pos(eoff, eline, ecol) = lend
      lexemes := Cons(Lexeme(make-range(Pos(src, off, line, col), Pos(src, eoff, eline, ecol)), l), lexemes)
  alex-scan(str.slice, 0)
  lexemes.reverse

fun lexer(path: string, line: int, input: string): <pure> list<lexeme>
  lexing(Source(path, input), line, input)

fun lexing(source: source, line: int, input: string)
  val init-pos = Pos(source, 0, 0, 1)
  lex(input, init-pos)

fun main()
  var done := False
  var s := read-text-file("compiler/core/core.kk".path)
  val source = Source("compiler/core/core.kk", s)
  lexing(source, 1, s)
  ()
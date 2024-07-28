import compiler/syntax/lexeme
import compiler/syntax/lex2
import compiler/common/range
import std/os/file
import std/os/path
import std/core-extras

fun lex(str: string, pos: pos): pure list<lexeme>
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
          // trace("Cons")
          slices := Cons(s ++ f.string, rst)
          // trace("End Cons")
        Nil -> 
          // trace("Nil")
          throw("add-chunk when no chunked input")
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

fun lexer(path: string, line: int, input: string): pure list<lexeme>
  lexing(Source(path, input), line, input)

fun lexing(source: source, line: int, input: string): pure list<lexeme>
  val init-pos = Pos(source, 0, 0, 1)
  lex(input, init-pos)

fun main()
  foreach([
    "compiler/syntax/lex2",
    "compiler/syntax/lex-help",
    "compiler/syntax/koka-lex",
    "compiler/syntax/lexer",
    "compiler/syntax/lexer2",
    "compiler/syntax/lexeme",
    "compiler/core/core",
    ]) fn(f)
    val s = read-text-file((f ++ ".kk").path)
    val source = Source(f ++ ".kk", s)
    lexing(source, 1, s)
    ()
import compiler/syntax/layout
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/common/range
import std/os/path
import std/os/file

fun main()
  val f = read-text-file("testcompiler/syntax/layout.kk".path)
  test(f)

fun test-file(fname: string)
  val f = read-text-file(("test/" ++ fname).path)
  test-ex(fname, f)

fun test(xs: string)
  test-ex("", xs)

fun test-ex(fname: string, input: string)
  val tokens = lexing(Source(fname, input), 1, input)
  tokens.layout(True, True).map(show).unlines.println

import compiler/syntax/layout

fun main()
  val f = read-text-file("compiler/syntax/lexer.kk".path)
  test(f).trace-show

fun test-file(fname: string)
  val f = read-text-file(("test/" ++ fname).path)
  testEx(fname, f).trace-show

fun test(xs: string)
  testEx("", xs)

fun testEx(fname: string, input: string)
  val tokens = lexing(Source(fname, input), 1, input)
  layout(True, tokens).map(show).unlines.println

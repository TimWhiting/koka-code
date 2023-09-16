import compiler/syntax/parse
import std/os/path
import compiler/syntax/lexeme
import compiler/common/range

fun main()
  with handler
    final ctl astError(s: string, r: range)
      println("ast error: " ++ s ++ " at " ++ r.showFullRange)
  val x = parseProgramFromString(True, "public module hello;", "test.kk".path)
  println(x.show)
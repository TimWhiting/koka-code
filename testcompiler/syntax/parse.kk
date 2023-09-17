import compiler/syntax/parse
import std/os/path
import compiler/syntax/lexeme
import compiler/syntax/syntax
import compiler/common/range
import compiler/common/name

fun main()
  with handler
    final ctl astError(s: string, r: range)
      println("ast error: " ++ s ++ " at " ++ r.showFullRange)
  val x = parseProgramFromString(True, "public module hello; import hello as hi;", "test.kk".path)
  println(x.show(show, show))
  
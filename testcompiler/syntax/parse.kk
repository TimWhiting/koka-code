import compiler/syntax/parse
import std/os/path
import compiler/syntax/lexeme
import compiler/syntax/syntax
import compiler/common/range
import compiler/common/name
import compiler/common/parse

fun main()
  with handler
    final ctl astError(s: string, r: range)
      println("ast error: " ++ s ++ " at " ++ r.showFullRange)
  val x = parseProgramFromFile(True, "/home/tim/koka_code/testcompiler/syntax/parse.kk".path)
  println(x.show(show, show))
  
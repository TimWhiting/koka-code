import compiler/syntax/lexer
import std/os/path
import std/os/file
import newstd/text/parse
import compiler/syntax/lexeme

fun main()
  // Make sure to set $ulimit -s unlimited$ to allow more stack space
  val r = read-text-file(".koka/v2.4.3/clang-debug/compiler_common_failure.kki".path)
  val x = lexer("test", 1, r)
  x.show.println
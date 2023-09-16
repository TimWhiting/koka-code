import compiler/syntax/lexer2
import std/os/path
import std/os/file
import newstd/text/parse
import compiler/syntax/lexeme

fun main()
  // Make sure to set $ulimit -s unlimited$ to allow more stack space
  val r = read-text-file("/Users/timwhiting/koka_code/scratch/test.kk".path)
  val x = lexer("test", 0, "fn(x) x")
  match x
    Right(u) -> u.map(show).join(",").println
    Left(msg) -> msg.show(fn(s:string) s, r).println
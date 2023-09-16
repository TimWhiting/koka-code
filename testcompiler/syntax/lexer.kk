import compiler/syntax/lexer
import std/os/path
import std/os/file
import std/text/parse
import compiler/syntax/lexeme

fun main()
  // Make sure to set $ulimit -s unlimited$ to allow more stack space
  val r = read-text-file("/Users/timwhiting/koka_code/compiler/syntax/lexer.kk".path)
  val x = lexer("test", 0, r#"'\''"#)
  match x
    ParseOk(u, _) -> u.map(show).join(",").println
    ParseError(msg, rst) -> ("Error: expected " ++ msg ++ " at: " ++ rst.string).println
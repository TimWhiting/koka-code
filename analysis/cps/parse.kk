import newstd/text/parse
import std/text/regex
import std/num/float64

fun main()
  val input = "1.53"
  val result = parseFloat.run(input)
  match result
    Right(x) -> println("Success: " ++ x.show)
    Left(err) -> println("Error: " ++ err.show(fn(x) x))
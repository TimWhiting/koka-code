import std/text/parse

fun test(): <parse> char {
  fun test2(): <parse> char {
    char('r')
  }
  unsafe-no-div(test2)
}

pub fun main() {
  val code = "hi"
  val mb = parse(code.slice, test)
  println("success")
}
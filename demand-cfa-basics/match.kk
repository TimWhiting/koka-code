fun f(x)
  match x
    True -> "x is 10"
    False -> "x is 20"

fun main()
  val x = f(True)
  val x' = f(False)
  println(x)
  println(x')
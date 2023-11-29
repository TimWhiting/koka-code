fun f(x)
  match x
    True -> "x is 10"
    False -> "x is 20"

fun g(x)
  match x
    Cons(x1, xs) -> 10
    _ -> 20

fun main()
  val x = f(True)

  val x' = f(False)
  
  val y = g([1])

  val y' = g([[3], [4]])

  println(x)
  println(x')
  println(y)
  println(y')
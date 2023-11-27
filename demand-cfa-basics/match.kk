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
  println(g(Cons(1, Nil)))
  println(g(Cons(Cons(3, Nil), Cons(Cons(4, Nil), Nil))) )
  println(x)
  println(x')
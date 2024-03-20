fun map2(ls: list<int>, f: (int) -> int): list<int>
  match ls
    Nil -> Nil
    Cons(x, xs) -> Cons(f(x), xs.map2(f))

fun s2(ls2: list<int>): list<int>
  ls2.map2(fn(z) z + 1)

fun main()
  val x1 = s2([1, 2, 3])

  val x = 1 + 2
  
  val y = x * 4 
  
  val z = y - (y + x)
  
  ()
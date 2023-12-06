fun a1(f1)
  f1(4)

fun s4(ls: list<int>): list<int>
  ls.map(fn(i) i + 1)

fun map2(ls: list<int>, f: (int) -> int): list<int>
  match ls
    Cons(x, xx) -> Cons(f(x), map2(xx, f))
    Nil -> Nil

fun s2(ls: list<int>): list<int>
  ls.map2(fn(z) z + 1)

fun something(x1, y1: int)
  x1 + y1

fun xs()
  s4

fun main()
  (fn(y0) 
    y0(1)
    fn(x4)
      y0(x4)
  )(fn(x3) x3)(2)

  (fn(y0) 
    y0(True)
    fn(x4)
      y0(x4)
  )(fn(x3) x3)(False)
  a1(id).println
  a1(fn(i) i + 1).println
  something(1, 1)
  something(2, 3)

  val x1 = s4([1, 2, 3])

  val x2 = s2([1, 2, 3])

  val x3 = xs()

  ()
  // val f1 = fn((x1, y1)) something(x1, y1)
  // [(1, 2), (2, 3), (4, 5)].map(f1).show.println
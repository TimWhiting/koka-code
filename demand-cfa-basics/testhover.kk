fun id(x)
  x

fun a1(f1)
  f1(4)

fun map2(xs: list<a>, f: a -> b): list<b>
  match xs
    Cons(x, xx) -> Cons(f(x), map2(xx, f))
    Nil -> Nil

fun s2(ls2: list<int>): list<int>
  ls2.map(fn(z) z + 1)

fun s4(ls: list<int>): list<int>
  ls.map2(fn(i) i + 1)

fun map2'(ls0: list<int>, f0: (int) -> int): list<int>
  match ls0
    Cons(x00, xx00) -> Cons(f0(x00), map2'(xx00, f0))
    Nil -> Nil

fun s2'(ls1: list<int>): list<int>
  ls1.map2'(fn(z) z + 1)

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
  a1(testhover/id).println
  a1(fn(i) i + 1).println
  something(1, 1)
  something(2, 3)

  val x0 = s4([1, 2, 3])


  val x1 = s2([1, 2, 3])


  val x2 = s2([1, 2, 3])

  val x3 = xs()

  ()
  // val f1 = fn((x1, y1)) something(x1, y1)
  // [(1, 2), (2, 3), (4, 5)].map(f1).show.println
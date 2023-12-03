fun a1(f1)
  f1(4)

fun something(x1, y1: int)
  x1 + y1

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
  ()
  // val f1 = fn((x1, y1)) something(x1, y1)
  // [(1, 2), (2, 3), (4, 5)].map(f1).show.println
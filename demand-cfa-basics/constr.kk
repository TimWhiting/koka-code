fun s2(ls2: list<int>): list<int>
  ls2.map(fn(z) z + 1)

fun main()
  val x1 = s2([1, 2, 3])
  ()
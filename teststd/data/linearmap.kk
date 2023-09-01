import newstd/data/linearmap

fun main()
  val h = linearMap([(1, "a"), (2, "b")], fn(a,b) a == b)
  val h' = linearMap([(2, "b"), (1, "a")], fn(a,b) a == b)
  (==)(h, h', (==)).show.println
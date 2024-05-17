import std/data/linearmap

fun main()
  val h = linearMap([(1, "a"), (2, "b")], (==), (==), show, show)
  val h' = linearMap([(2, "b"), (1, "a")], (==), (==), show, show)
  (==)(h, h').show.println
import newstd/data/linearset

fun main()
  val h = linearSet([(1, "a"), (2, "b")], fn(a,b) a.fst == b.fst && a.snd == b.snd)
  val h' = linearSet([(2, "b"), (1, "a")], fn(a,b) a.fst == b.fst && a.snd == b.snd)
  (==)(h, h').show.println
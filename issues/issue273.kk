effect eff
  ctl a() : bool

fun g(s : sslice, limit : int = s.count) : eff ()
  ()

fun h() : eff ()
  val s = "a".slice
  var s' := "b".slice
  g(s', s'.count - s.count)

fun main()
  ()
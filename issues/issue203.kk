// named effect val named-value : int
// ^ not working even!

named effect named-effect
  val named-value : int

fun main()
  with r = named handler val named-value = 1
  println(named-value(r).show)
  // ^ not working
  println(r.named-value.show)
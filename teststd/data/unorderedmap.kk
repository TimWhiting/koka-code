import newstd/data/unorderedmap
import std/num/int32

fun main()
  val h = singleton(1.int32, "a", id, fn(a,b) a == b)
  val h' = h.insertWith(1.int32, "initial", fn(a) a ++ "a")
  h'.findWithDefault(1.int32, "b").println()
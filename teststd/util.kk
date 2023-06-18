
import newstd/util
import newstd/test

ref struct hi 
  i: int
  s: string

fun main()
  val x = Hi(1, "hi")
  val y = Hi(1, "hi")
  val z = x
  val z2 = Hi(2, "hi")
  expect(fn() identical(x,x), "x should be identical to itself")
  expect(fn() identical(x,z), "x should be an alias to z")
  expect(fn() !identical(x,y), "identical uses pointer equalify")
  expect(fn() !identical(x,z2), "identical respects equality")
  // Note that fbip cannot cause this to be true because both x and it's copy are alive
  expect(fn() !identical(x,x(i=2)), "copies are not equal") 
  expect(fn() !identical(x(i=2),z2), "copies are not equal")

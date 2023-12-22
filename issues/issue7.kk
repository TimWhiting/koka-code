co type stream<a>
  SCons(hd: a, tl: stream<a>)

fun hist_helper(s: stream<a>, state: list<a>): total stream<list<a>>
  match(s) 
    SCons(hd, tl) -> 
      val next = Cons(hd, state)
      SCons(next, hist_helper(tl, next))


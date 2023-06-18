alias listset<v> = list<v> 

fun member(l: listset<v>, a: v, eq: (v, v) -> e bool): e bool
  any(l, fn(x) eq(x, a))

fun union(l: listset<v>, l2: listset<v>, eq: (v, v) -> e bool): e listset<v>
  l2.foldl(l, fn(acc, x) add(acc, x, eq))

fun add(l: listset<v>, a: v, eq: (v, v) -> e bool): e listset<v>
  if (member(l, a, eq)) then l else Cons(a, l)

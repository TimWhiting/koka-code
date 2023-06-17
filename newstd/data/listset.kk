alias listset<v> = list<v> 

fun setmember(l: listset<v>, a: v, eq: (v, v) -> e bool): e bool
  any(l, fn(x) eq(x, a))

fun setunion(l: listset<v>, l2: listset<v>, eq: (v, v) -> e bool): e listset<v>
  l2.foldl(l, fn(acc, x) setadd(acc, x, eq))

fun setadd(l: listset<v>, a: v, eq: (v, v) -> e bool): e listset<v>
  if (setmember(l, a, eq)) then l else Cons(a, l)

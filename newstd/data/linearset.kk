pub value struct linearSet<v,e::E>
  list: list<v> 
  eq: (v, v) -> e bool

pub fun linearSet(l: list<v>, eq: (v, v) -> e bool): <> linearSet<v,e>
  LinearSet(l, eq)

pub fun member(l: linearSet<v,e>, a: v): e bool
  any(l.list, fn(x) (l.eq)(x, a))

pub fun union(l: linearSet<v,e>, l2: linearSet<v,e>): e linearSet<v,e>
  l2.list.foldl(l, fn(acc, x) acc.add(x))

pub fun add(l: linearSet<v,e>, a: v): e linearSet<v,e>
  if (l.member(a)) then l else l(list=Cons(a, l.list))

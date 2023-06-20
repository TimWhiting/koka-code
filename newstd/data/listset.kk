pub value struct set<v,e::E>
  list: list<v> 
  eq: (v, v) -> e bool

pub fun set(l: list<v>, eq: (v, v) -> e bool): <> set<v,e>
  Set(l, eq)

pub fun member(l: set<v,e>, a: v): e bool
  any(l.list, fn(x) (l.eq)(x, a))

pub fun union(l: set<v,e>, l2: set<v,e>): e set<v,e>
  l2.list.foldl(l, fn(acc, x) acc.add(x))

pub fun add(l: set<v,e>, a: v): e set<v,e>
  if (l.member(a)) then l else l(list=Cons(a, l.list))

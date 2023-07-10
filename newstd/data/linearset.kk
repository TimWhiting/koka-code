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

pub fun (+)(l1: linearSet<v,e>, l2: linearSet<v,e>): e linearSet<v,e>
  l1.union(l2)

pub fun (-)(l: linearSet<v,e>, v: v): e linearSet<v,e>
  l(list=l.list.filter(fn(x) !(l.eq)(x, v)))

pub fun (-)(l: linearSet<v,e>, l2: linearSet<v,e>): e linearSet<v,e>
  l(list=l.list.filter(fn(x) !l2.member(x)))

pub fun (-)(l: linearSet<v,e>, l2: list<v>): e linearSet<v,e>
  val lnew = linearSet(l2, l.eq)
  l(list=l.list.filter(fn(x) !lnew.member(x)))
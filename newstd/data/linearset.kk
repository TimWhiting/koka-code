pub value struct linearSet<v>
  pub list: list<v> 
  eq: some<e> (v, v) -> e bool

pub fun show(l: linearSet<v>, showV: (v) -> e string): e string
  "{" ++ l.list.show-list(showV) ++ "}"

pub fun (==)(l1: linearSet<v>, l2: linearSet<v>): e bool
  l1.list.length == l2.list.length && l1.list.all(fn(x) l2.member(x))

pub fun linearSet(l: list<v>, eq: (v, v) -> e bool): <> linearSet<v>
  LinearSet(l, eq)

pub fun is-empty(l: linearSet<v>): bool
  l.list.is-nil

pub fun foreach(l: linearSet<v>, f: (v) -> e ()): e ()
  l.list.foreach(f)

pub fun member(l: linearSet<v>, a: v): e bool
  any(l.list, fn(x) (l.eq)(x, a))

pub fun union(l: linearSet<v>, l2: linearSet<v>): e linearSet<v>
  l2.list.foldl(l, fn(acc, x) acc.add(x))

pub fun add(l: linearSet<v>, a: v): e linearSet<v>
  if (l.member(a)) then l else l(list=Cons(a, l.list))

pub fun (+)(l1: linearSet<v>, l2: linearSet<v>): e linearSet<v>
  l1.union(l2)

pub fun (-)(l: linearSet<v>, v: v): e linearSet<v>
  l(list=l.list.filter(fn(x) !(l.eq)(x, v)))

pub fun (-)(l: linearSet<v>, v: maybe<v>): e linearSet<v>
  match v
    Just(vv) -> l(list=l.list.filter(fn(x) !(l.eq)(x, vv)))
    Nothing -> l

pub fun (-)(l: linearSet<v>, l2: linearSet<v>): e linearSet<v>
  l(list=l.list.filter(fn(x) !l2.member(x)))

pub fun (-)(l: linearSet<v>, l2: list<v>): e linearSet<v>
  val lnew = linearSet(l2, l.eq)
  l(list=l.list.filter(fn(x) !lnew.member(x)))
// pub fun main()
//   val s = linearSet([1, 2, 3], (==))
//   val s2 = linearSet([2, 3, 4], (==))
//   val s3 = s + s2
//   s3.list.show-list(show).println
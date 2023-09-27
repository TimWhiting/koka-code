pub value struct linearSet<v>
  pub list: list<v> 
  eq: some<e> (v, v) -> e bool
  showE: some<e> (v) -> e string

pub fun show(l: linearSet<v>): e string
  "{" ++ l.list.show-list(l.showE) ++ "}"

pub fun (==)(l1: linearSet<v>, l2: linearSet<v>): e bool
  l1.list.length == l2.list.length && l1.list.all(fn(x) l2.member(x))

pub fun linearSet(l: list<v>, eq: (v, v) -> e bool, show: (v) -> e string): <> linearSet<v>
  LinearSet(l, eq, show)

pub fun is-empty(l: linearSet<v>): bool
  l.list.is-nil

pub fun foreach(l: linearSet<v>, f: (v) -> e ()): e ()
  l.list.foreach(f)

pub fun member(l: linearSet<v>, a: v): e bool
  any(l.list, fn(x) (l.eq)(x, a))

pub fun union(l: linearSet<v>, l2: linearSet<v>): e linearSet<v>
  l2.list.foldl(l, fn(acc, x) acc.add(x))

pub fun unions(ls: list<linearSet<v>>): <exn|e> linearSet<v>
  ls.foldl(ls.head.unjust, fn(acc, x) acc.union(x))

pub fun add(l: linearSet<v>, a: v): e linearSet<v>
  if (l.member(a)) then l else l(list=Cons(a, l.list))

pub fun (+)(l: linearSet<v>, a: v): e linearSet<v>
  if (l.member(a)) then l else l(list=Cons(a, l.list))

pub fun (+)(l1: linearSet<v>, l2: linearSet<v>): e linearSet<v>
  l1.union(l2)

pub fun (+)(l1: linearSet<v>, l2: list<v>): e linearSet<v>
  l2.foldl(l1, fn(acc, x) acc.add(x))

pub fun (-)(l: linearSet<v>, v: v): e linearSet<v>
  l(list=l.list.filter(fn(x) !(l.eq)(x, v)))

pub fun (-)(l: linearSet<v>, v: maybe<v>): e linearSet<v>
  match v
    Just(vv) -> l(list=l.list.filter(fn(x) !(l.eq)(x, vv)))
    Nothing -> l

pub fun (-)(l: linearSet<v>, l2: linearSet<v>): e linearSet<v>
  l(list=l.list.filter(fn(x) !l2.member(x)))

pub fun (-)(l: linearSet<v>, l2: list<v>): e linearSet<v>
  val lnew = linearSet(l2, l.eq, l.showE)
  l(list=l.list.filter(fn(x) !lnew.member(x)))

pub fun intersection(l1: linearSet<v>, l2: linearSet<v>): e linearSet<v>
  l1(list=l1.list.filter(fn(x) l2.member(x)))

pub fun disjoint(l1: linearSet<v>, l2: linearSet<v>): bool
  l1.intersection(l2).list.is-nil

pub fun common(l1: linearSet<v>, l2: linearSet<v>): e bool
  !l1.disjoint(l2)

fun filter(l: linearSet<v>, f: (v) -> e bool): e linearSet<v>
  l(list=l.list.filter(f))

fun isSubsetOf(l1: linearSet<v>, l2: linearSet<v>): bool
  l1.list.all(fn(x) l2.member(x))

pub fun map(l: linearSet<v>, f: (v) -> e w, eqW: (w, w) -> e bool, showW: (w) -> e string): e linearSet<w>
  linearSet(l.list.map(f), eqW, showW)
// pub fun main()
//   val s = linearSet([1, 2, 3], (==))
//   val s2 = linearSet([2, 3, 4], (==))
//   val s3 = s + s2
//   s3.list.show-list(show).println
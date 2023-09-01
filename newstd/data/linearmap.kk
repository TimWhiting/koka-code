pub struct linearMap<k,v>
  pub list: list<(k,v)> 
  pub eq: some<e> (k, k) -> e bool
  pub eqV: some<e> (v, v) -> e bool
  pub showK: some<e> (k) -> e string
  pub showV: some<e> (v) -> e string

pub fun show(l: linearMap<k,v>): e string
  "{" ++ l.list.show-list(fn(e) (l.showK)(e.fst) ++ ": " ++ (l.showV)(e.snd)) ++ "}"

pub fun (==)(l1: linearMap<k,v>, l2: linearMap<k,v>): e bool
  l1.list.length == l2.list.length && l1.list.all fn(x) 
    match l2.maybeGet(x.fst)
      Just(v') -> (l1.eqV)(v', x.snd)
      Nothing -> False

pub fun linearMap(l: list<(k,v)>, eq: (k, k) -> e bool, eqV: (v, v) -> e bool, showK: (k) -> e string, showV: (v) -> e string): <> linearMap<k,v>
  LinearMap(l, eq, eqV, showK, showV)

pub fun containsKey(l: linearMap<k,v>, k: k): e bool
  l.list.any(fn((kk, _)) (l.eq)(kk, k))

pub fun update(m: linearMap<k,v>, k: k, b: v, f: (v, v) -> e v): e linearMap<k,v>
  m(list=m.list.update(k, f, b, m.eq))

fun update(l: list<(k,v)>, k: k, f: (v, v) -> e v, b: v, eq: (k, k) -> e bool): e list<(k,v)>
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then Cons((kk, f(b, vv)), rst) else Cons((kk, vv), rst.update(k, f, b, eq))
    Nil -> Cons((k, b), Nil) 

pub fun get(m: linearMap<k,v>, k: k): <exn|e> v
  m.list.get(k, m.eq)

fun get(l: list<(k,v)>, k: k, eq: (k, k) -> e bool): <exn|e> v
  match l
    Cons((kk, vv), rst) -> if mask<exn>{(eq)(kk, k)} then vv else rst.get(k, eq)
    Nil -> throw("not found")

pub fun maybeGet(m: linearMap<k,v>, k: k): e maybe<v>
  catch({Just(m.list.get(k, m.eq))}, fn(x) {Nothing})

pub fun getDefault(m: linearMap<k,v>, k: k, v: v): e v
  m.list.getDefault(k, v, m.eq)

fun getDefault(l: list<(k,v)>, k: k, v: v, eq: (k, k) -> e bool): e v
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then vv else rst.getDefault(k, v, eq)
    Nil -> v

/// Overwrite any existing key with value
pub fun set(m: linearMap<k,v>, k: k, v: v): e linearMap<k,v>
  m(list=m.list.update(k, fn(_, v1) v1, v, m.eq))

/// Add only if key is not present in the map
pub fun add(m: linearMap<k,v>, k: k, b: v): e linearMap<k,v>
  m(list=m.list.update(k, fn(x, _) x, b, m.eq))

pub fun addAll(m: linearMap<k,v>, l: list<(k,v)>): e linearMap<k,v>
  match l
    Nil -> m
    Cons((k, v), rst) -> addAll(m.add(k, v), rst)

pub fun foldr(m: linearMap<k,v>, acc: a, f: (k, v, a) -> e a): e a
  m.list.foldr(acc, fn((k, v), x) f(k, v, x))

pub fun map(m: linearMap<k,v>, f: (k, v) -> e (k, v)): e linearMap<k,v>
  m(list=m.list.map(fn((k,v)) f(k,v)))


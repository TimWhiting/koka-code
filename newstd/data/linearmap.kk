pub value struct linearMap<k,v>
  pub list: list<(k,v)> 
  // pub eq: some<e> (k, k) -> e bool
  // pub eqV: some<e> (v, v) -> e bool
  // pub showK: some<e> (k) -> e string
  // pub showV: some<e> (v) -> e string

pub fun show(l: linearMap<k,v>, ?showK: (k) -> e string = show, ?showV: (v) -> e string = show): e string
  "{" ++ l.list.show-list(fn(e) showK(e.fst) ++ ": " ++ showV(e.snd)) ++ "}"

pub fun (==)(l1: linearMap<k,v>, l2: linearMap<k,v>, ?eqK: (k, k) -> e bool = (==), ?eqV: (v, v) -> e bool = (==)): e bool
  l1.list.length == l2.list.length && l1.list.all fn(x) 
    match l2.maybeGet(x.fst, eqK)
      Just(v') -> eqV(v', x.snd)
      Nothing -> False

pub fun linearMap(l: list<(k,v)>): <> linearMap<k,v>
  LinearMap(l)

pub fun containsKey(l: linearMap<k,v>, k: k, (==): (k, k) -> e bool): e bool
  l.list.any(fn((kk, _)) kk == k)

pub fun update(m: linearMap<k,v>, k: k, b: v, f: (v, v) -> e v, ?(==): (k, k) -> e bool): e linearMap<k,v>
  m(list=m.list.update(k, f, b))

fun update(l: list<(k,v)>, k: k, f: (v, v) -> e v, b: v, ?(==): (k, k) -> e bool): e list<(k,v)>
  match l
    Cons((kk, vv), rst) -> if k == kk then Cons((kk, f(b, vv)), rst) else Cons((kk, vv), rst.update(k, f, b, (==)))
    Nil -> Cons((k, b), Nil) 

pub fun get(m: linearMap<k,v>, k: k, ?(==): (k, k) -> e bool): <exn|e> v
  m.list.get(k)

fun get(l: list<(k,v)>, k: k, ?(==): (k, k) -> e bool): <exn|e> v
  match l
    Cons((kk, vv), rst) -> if mask<exn>{kk == k} then vv else rst.get(k, (==))
    Nil -> throw("not found")

pub fun maybeGet(m: linearMap<k,v>, k: k, ?(==): (k, k) -> e bool): e maybe<v>
  catch({Just(m.list.get(k, (==)))}, fn(x) {Nothing})

pub fun getDefault(m: linearMap<k,v>, k: k, v: v, ?(==): (k, k) -> e bool): e v
  m.list.getDefault(k, v, (==))

fun getDefault(l: list<(k,v)>, k: k, v: v, ?(==): (k, k) -> e bool): e v
  match l
    Cons((kk, vv), rst) -> if kk == k then vv else rst.getDefault(k, v, (==))
    Nil -> v

/// Overwrite any existing key with value
pub fun set(m: linearMap<k,v>, k: k, v: v, ?(==): (k, k) -> e bool): e linearMap<k,v>
  m(list=m.list.update(k, fn(_, v1) v1, v, (==)))

/// Add only if key is not present in the map
pub fun add(m: linearMap<k,v>, k: k, b: v, ?(==): (k, k) -> e bool): e linearMap<k,v>
  m(list=m.list.update(k, fn(x, _) x, b, (==)))

pub fun addAll(m: linearMap<k,v>, l: list<(k,v)>, ?(==): (k, k) -> e bool): e linearMap<k,v>
  match l
    Nil -> m
    Cons((k, v), rst) -> addAll(m.add(k, v), rst)

pub fun foldr(m: linearMap<k,v>, acc: a, f: (k, v, a) -> e a): e a
  m.list.foldr(acc, fn((k, v), x) f(k, v, x))

pub fun map(m: linearMap<k,v>, f: (k, v) -> e (k, v)): e linearMap<k,v>
  m(list=m.list.map(fn((k,v)) f(k,v)))

pub fun unions(l: list<linearMap<k,v>>, ?(==): (k, k) -> <exn|e> bool): <exn|e> linearMap<k,v>
  val fst = l.head.unjust
  l.foldl(fst, fn(x, y) x.addAll(y.list))

pub fun (+)(l1: linearMap<k,v>, l2: linearMap<k,v>, ?(==): (k, k) -> e bool): e linearMap<k,v>
  l1.addAll(l2.list)

pub fun (+)(l1: linearMap<k,v>, l2: list<(k,v)>, ?(==): (k, k) -> e bool): e linearMap<k,v>
  l1.addAll(l2)

pub fun union(l1: linearMap<k,v>, l2: linearMap<k,v>, ?(==): (k, k) -> e bool): e linearMap<k,v>
  l1.addAll(l2.list)

pub fun filter(m: linearMap<k,v>, f: (k, v) -> e bool): e linearMap<k,v>
  m(list=m.list.filter(fn((k,v)) f(k,v)))

pub fun remove(m: linearMap<k,v>, k: k, ?(==): (k, k) -> e bool): e linearMap<k,v>
  m(list=m.list.filter(fn((k1,_)) !(k == k1)))

pub fun removeAll(m: linearMap<k,v>, l: list<k>, ?(==): (k, k) -> e bool): e linearMap<k,v>
  m(list=m.list.filter(fn((k1,_)) !l.any(fn(k2) k1 == k2)))

pub fun unionWith(m1: linearMap<k,v>, m2: linearMap<k,v>, f: (v, v) -> e v, ?(==): (k, k) -> e bool): e linearMap<k,v>
  m2.list.foldl(m1, fn(x, (k, y)) x.update(k, y, f))
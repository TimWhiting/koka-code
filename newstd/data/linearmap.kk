pub value struct linearMap<k,v,e>
  pub list: list<(k,v)> 
  eq: (k, k) -> e bool

pub fun linearMap(l: list<(k,v)>, eq: (k, k) -> e bool): <> linearMap<k,v,e>
  LinearMap(l, eq)

pub fun update(m: linearMap<k,v,e>, k: k, f: (v) -> e v, b: v): e linearMap<k,v,e>
  m(list=m.list.update(k, f, b, m.eq))

fun update(l: list<(k,v)>, k: k, f: (v) -> e v, b: v, eq: (k, k) -> e bool): e list<(k,v)>
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then Cons((kk, f(vv)), rst) else Cons((kk, vv), rst.update(k, f, b, eq))
    Nil -> Cons((k, f(b)), Nil) 

pub fun get(m: linearMap<k,v,e>, k: k): <exn|e> v
  m.list.get(k, m.eq)

fun get(l: list<(k,v)>, k: k, eq: (k, k) -> e bool): <exn|e> v
  match l
    Cons((kk, vv), rst) -> if mask<exn>{(eq)(kk, k)} then vv else rst.get(k, eq)
    Nil -> throw("not found")

pub fun maybeGet(m: linearMap<k,v,e>, k: k): e maybe<v>
  catch({Just(m.list.get(k, m.eq))}, fn(x) {Nothing})

pub fun getDefault(m: linearMap<k,v,e>, k: k, v: v): e v
  m.list.getDefault(k, v, m.eq)

fun getDefault(l: list<(k,v)>, k: k, v: v, eq: (k, k) -> e bool): e v
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then vv else rst.getDefault(k, v, eq)
    Nil -> v

pub fun set(m: linearMap<k,v,e>, k: k, v: v): e linearMap<k,v,e>
  m(list=m.list.set(k, v, m.eq))

fun set(l: list<(k,v)>, k: k, v: v, eq: (k, k) -> e bool): e list<(k,v)>
  update(l, k, fn(_) v, v, eq)
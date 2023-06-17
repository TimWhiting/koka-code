alias listmap<k,v> = list<(k,v)> 

fun update(l: listmap<k,v>, k: k, f: (v) -> e v, b: v, eq: (k, k) -> e bool): e listmap<k,v>
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then Cons((kk, f(vv)), rst) else Cons((kk, vv), update(rst, k, f, b, eq))
    Nil -> Cons((k, f(b)), Nil) 

fun get(l: listmap<k,v>, k: k, eq: (k, k) -> e bool): <exn|e> v
  match l
    Cons((kk, vv), rst) -> if mask<exn>{eq(kk, k)} then vv else get(rst, k, eq)
    Nil -> throw("not found")

fun getDefault(l: listmap<k,v>, k: k, eq: (k, k) -> e bool, v: v): e v
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then vv else getDefault(rst, k, eq, v)
    Nil -> v

fun set(l: listmap<k,v>, k: k, v: v, eq: (k, k) -> e bool): e listmap<k,v>
  update(l, k, fn(_) v, v, eq)
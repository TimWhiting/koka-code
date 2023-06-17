
fun update(l: list<(a,b)>, k: a, f: (b) -> e b, b: b, eq: (a, a) -> e bool): e list<(a,b)>
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then Cons((kk, f(vv)), rst) else Cons((kk, vv), update(rst, k, f, b, eq))
    Nil -> Cons((k, f(b)), Nil) 

fun setmember(l: list<a>, a: a, eq: (a, a) -> e bool): e bool
  any(l, fn(x) eq(x, a))

fun setunion(l: list<a>, l2: list<a>, eq: (a, a) -> e bool): e list<a>
  l2.foldl(l, fn(acc, x) setadd(acc, x, eq))

fun setadd(l: list<a>, a: a, eq: (a, a) -> e bool): e list<a>
  if (setmember(l, a, eq)) then l else Cons(a, l)

fun getKey(l: list<(a, v)>, k: a, eq: (a, a) -> e bool): <exn|e> v
  match l
    Cons((kk, vv), rst) -> if mask<exn>{eq(kk, k)} then vv else getKey(rst, k, eq)
    Nil -> throw("not found")

fun getKeyDefault(l: list<(a, v)>, k: a, eq: (a, a) -> e bool, v: v): e v
  match l
    Cons((kk, vv), rst) -> if eq(kk, k) then vv else getKeyDefault(rst, k, eq, v)
    Nil -> v

fun setVal(l: list<(a, v)>, k: a, v: v, eq: (a, a) -> e bool): e list<(a, v)>
  update(l, k, fn(_) v, v, eq)
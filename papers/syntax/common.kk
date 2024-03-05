alias identifier = string
alias variable = identifier

fun listdiv/(==)(l: list<a>, r: list<a>, ?(==): (a, a) -> div bool): div bool
  match l
    Nil -> match r
      Nil -> True
      Cons(_, _) -> False
    Cons(x, xs) -> match r
      Nil -> False
      Cons(y, ys) -> if x == y then listdiv/(==)(xs, ys) else False

fun map/lookup(l: list<(a, b)>, x: a, ?(==): (a, a) -> pure bool): pure b
  match l 
    [] -> throw("lookup")
    Cons((y, z), ys) -> if x == y then z else lookup(ys, x)

fun map/contains(l: list<(a, b)>, x: a, ?(==): (a, a) -> pure bool): pure bool
  match l 
    [] -> False
    Cons((y, _), ys) -> if x == y then True else contains(ys, x)

fun map/remove(l: list<(a,b)>, x: a, ?(==): (a, a) -> pure bool): pure list<(a,b)>
  match l
    Nil -> Nil
    Cons((y, z), ys) -> if x == y then ys else Cons((y, z), remove(ys, x))

fun map/extend(l: list<(a, b)>, l2: list<(a,b)>, ?(==): (a, a) -> pure bool): pure list<(a,b)>
  match l2
    Nil -> l
    Cons((x, y), ys) -> 
      if l.contains(x) then extend(l.remove(x), ys)
      else extend(Cons((x, y), l), ys)

fun map/set(l: list<(a, b)>, x: a, y: b, ?(==): (a, a) -> pure bool): pure list<(a,b)>
  match l
    Nil -> Cons((x,y), Nil)
    Cons((z, w), zs) -> if x == z then Cons((x, y), zs) else Cons((z, w), set(zs, x, y))

fun set/contains(l: list<a>, x: a, ?(==): (a, a) -> pure bool): pure bool
  match l
    Nil -> False
    Cons(y, ys) -> if x == y then True else contains(ys, x)

fun set/add(l: list<a>, x: a, ?(==): (a, a) -> pure bool): pure list<a>
  if l.contains(x) then l else Cons(x, l)

fun set/join(l: list<(a,list<b>)>, a: a, b: b, ?a/(==): (a,a) -> pure bool, ?b/(==): (b,b) -> pure bool): pure list<(a,list<b>)>
  match l
    Nil -> Cons((a,[b]), Nil)
    Cons((a',bs), l') -> 
      if a == a' then Cons((a', bs.set/add(b)), l')
      else Cons((a',bs), join(l', a, b))

fun listset/join(l: list<(a,list<b>)>, l2: list<(a,b)>, ?a/(==): (a,a) -> pure bool, ?b/(==): (b,b) -> pure bool): pure list<(a,list<b>)>
  l2.foldl(l, fn(l', (a,b)) join(l', a, b))

fun join/join(l: list<(a,b)>, a: a, b: b, ?a/(==): (a,a) -> pure bool, ?join: (b, b) -> b): pure list<(a,b)>
  match l
    Nil -> Cons((a,b), Nil)
    Cons((a',bold), l') -> 
      if a == a' then Cons((a', b.join(bold)), l')
      else Cons((a',bold), join(l', a, b))

fun joinlist/join(l: list<(a,b)>, l2: list<(a,b)>, ?a/(==): (a,a) -> pure bool, ?join: (b, b) -> b): pure list<(a,b)>
  l2.foldl(l, fn(l', (a,b)) join(l', a, b))



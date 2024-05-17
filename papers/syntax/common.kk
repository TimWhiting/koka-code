pub import newstd/data/linearmap
pub import newstd/data/linearset

alias identifier = string
alias variable = identifier

fun listdiv/(==)(l: list<a>, l2: list<a>, ?a/(==): (a,a) -> div bool): div bool
  match (l, l2)
    (Nil, Nil) -> True
    (Cons(a, l'), Cons(a', l2')) ->
      if a == a' then listdiv/(==)(l', l2')
      else False
    _ -> False

fun set/join(l: linearMap<a,linearSet<b>>, a: a, b: b, ?a/(==): (a,a) -> pure bool, ?b/(==): (b,b) -> pure bool): pure list<(a,list<b>)>
  match l
    Nil -> Cons((a,[b]), Nil)
    Cons((a',bs), l') -> 
      if a == a' then Cons((a', bs.add(b)), l')
      else Cons((a',bs), join(l', a, b))

fun listset/join(l: linearMap<a,linearSet<b>>, l2: linearMap<a,b>, ?a/(==): (a,a) -> pure bool, ?b/(==): (b,b) -> pure bool): pure list<(a,list<b>)>
  l2.foldl(l, fn(l', (a,b)) join(l', a, b))

fun join/join(l: linearMap<a,b>, a: a, b: b, ?a/(==): (a,a) -> pure bool, ?join: (b, b) -> b): pure list<(a,b)>
  match l
    Nil -> Cons((a,b), Nil)
    Cons((a',bold), l') -> 
      if a == a' then Cons((a', b.join(bold)), l')
      else Cons((a',bold), join(l', a, b))

fun joinlist/join(l: linearMap<a,b>, l2: linearMap<a,b>, ?a/(==): (a,a) -> pure bool, ?join: (b, b) -> b): pure list<(a,b)>
  l2.foldl(l, fn(l', (a,b)) join(l', a, b))



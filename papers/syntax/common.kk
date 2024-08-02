pub import std/data/linearmap
pub import std/data/linearset
import std/core/undiv

alias identifier = string
alias variable = identifier

fun listdiv/(==)(l: list<a>, l2: list<a>, ?a/(==): (a,a) -> e bool): e bool
  match (l, l2)
    (Nil, Nil) -> True
    (Cons(a, l'), Cons(a', l2')) ->
      if a == a' then listdiv/(==)(l'.pretend-decreasing, l2'.pretend-decreasing)
      else False
    _ -> False

fun listdiv/show(l: list<a>, ?a/show: a -> e string): e string
  match l
    Nil -> "[]"
    Cons(a, l') -> a.show ++ ", " ++ l'.listdiv/show

fun tuple2div/(==)(t1: (a,b), t2: (a,b), ?a/(==): (a,a) -> e bool, ?b/(==): (b,b) -> e bool): e bool
  t1.fst == t2.fst && t1.snd == t2.snd

fun set/join(l: linearMap<a,linearSet<b>>, a: a, b: b, ?a/(==): (a,a) -> e bool, ?b/(==): (b,b) -> e bool): e linearMap<a,linearSet<b>>
  LinearMap(l.list.join(a,b))

fun setlist/join(l: list<(a,linearSet<b>)>, a: a, b: b, ?a/(==): (a,a) -> e bool, ?b/(==): (b,b) -> e bool): e list<(a,linearSet<b>)>
  match l
    Nil -> Cons((a,LinearSet([b])), Nil)
    Cons((a',bs), l') -> 
      if a == a' then Cons((a', bs.add(b)), l')
      else Cons((a',bs), join(l', a, b))

fun listset/join(l: linearMap<a,linearSet<b>>, l2: linearMap<a,b>, ?a/(==): (a,a) -> e bool, ?b/(==): (b,b) -> e bool): e linearMap<a,linearSet<b>>
  l2.list.foldl(l, fn(l', (a,b)) l'.join(a, b))

fun joinmap/join(l: linearMap<a,b>, a: a, b: b, ?a/(==): (a,a) -> e bool, ?join: (b,b) -> e b): e linearMap<a,b>
  LinearMap(join/join(l.list, a, b))
  
fun join/join(l: list<(a,b)>, a: a, b: b, ?a/(==): (a,a) -> e bool, ?join: (b,b) -> e b): e list<(a,b)>
  match l
    Nil -> Cons((a,b), Nil)
    Cons((a',bold), l') -> 
      if a == a' then Cons((a', b.join(bold)), l')
      else Cons((a',bold), join/join(l', a, b))

fun joinmapc/join(l: linearMap<a,b>, a: a, b: c, ?a/(==): (a,a) -> e bool, ?join: (b,c) -> e b, ?empty: () -> b): e linearMap<a,b>
  LinearMap(l.list.join(a, b))

fun joinc/join(l: list<(a,b)>, a: a, b: c, ?a/(==): (a,a) -> e bool, ?join: (b,c) -> e b, ?empty: () -> b): e list<(a,b)>
  match l
    Nil -> Cons((a,empty().join(b)), Nil)
    Cons((a',bold), l') -> 
      if a == a' then Cons((a', bold.join(b)), l')
      else Cons((a',bold), join(l', a, b))

fun joinlist/join(l: linearMap<a,b>, l2: linearMap<a,b>, ?(==): (a,a) -> e bool, ?join: (b, b) -> b): e linearMap<a,b>
  l2.list.foldl(l, fn(l', (a, b)) l'.join(a,b))

// Restricts the domain of a linear map to a linear set
fun env/(~!)(e1: linearMap<a,s>, e: linearSet<a>, ?(==): (a,a) -> e bool): e linearMap<a,s>
  e1.filter(fn(a,_) e.member(a))
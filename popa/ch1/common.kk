
alias variable = string
alias label = int;

value struct set<a>
  values: list<a>

fun set/contains(s: set<a>, x: a, ?(==): (a, a) -> e bool): e bool
  s.values.any(fn(y) y == x)

fun set/add(s: set<a>, x: a, ?(==): (a, a) -> e bool): e set<a>
  if s.contains(x) then s else Set(Cons(x, s.values))

fun set/(++)(s1: set<a>, s2: set<a>, ?(==): (a, a) -> e bool): e set<a>
  Set(s2.values.foldl(s1.values) fn(acc, x) 
    if !acc.any(fn(y) y == x) then Cons(x, acc) else acc
  )
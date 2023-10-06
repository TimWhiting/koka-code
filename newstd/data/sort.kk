fun sortBy(l: list<a>, comp: (a, a) -> e order): e list<a>
  match l
    Nil -> Nil
    Cons(h, Nil) -> Cons(h, Nil)
    Cons(pivot, rst) -> 
      val (smaller, greater) = rst.partition fn(it) { comp(it, pivot) == Lt }
      return sortBy(smaller.unsafe-decreasing, comp) ++ Cons(pivot, sortBy(greater.unsafe-decreasing, comp))

fun groupBy(l: list<a>, comp: (a, a) -> e bool): e list<list<a>>
  match l
    Nil -> Nil
    Cons(h, Nil) -> Cons(Cons(h, Nil), Nil)
    Cons(pivot, rst) -> 
      val (smaller, greater) = rst.partition fn(it) { comp(it, pivot) }
      return groupBy(smaller.unsafe-decreasing, comp) ++ Cons(Cons(pivot, greater), Nil)
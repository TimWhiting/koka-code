fun sortBy(l: list<a>, comp: (a, a) -> e order): e list<a>
  match l
    Nil -> Nil
    Cons(h, Nil) -> Cons(h, Nil)
    Cons(pivot, rst) -> 
      val (smaller, greater) = rst.partition fn(it) { comp(it, pivot) == Lt }
      return sortBy(smaller.unsafe-decreasing, comp) ++ Cons(pivot, sortBy(greater.unsafe-decreasing, comp))
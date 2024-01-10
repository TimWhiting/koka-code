fun sort-by(l: list<a>, ?cmp: (a, a) -> e order): e list<a>
  match l
    Nil -> Nil
    Cons(h, Nil) -> Cons(h, Nil)
    Cons(pivot, rst) -> 
      val (smaller, greater) = rst.partition fn(it) { cmp(it, pivot) == Lt }
      return sort-by(smaller.unsafe-decreasing) ++ Cons(pivot, sort-by(greater.unsafe-decreasing))

fun group-by(l: list<a>, ?cmp: (a, a) -> e bool): e list<list<a>>
  match l
    Nil -> Nil
    Cons(h, Nil) -> Cons(Cons(h, Nil), Nil)
    Cons(pivot, rst) -> 
      val (smaller, greater) = rst.partition fn(it) { cmp(it, pivot) }
      return group-by(smaller.unsafe-decreasing) ++ Cons(Cons(pivot, greater), Nil)
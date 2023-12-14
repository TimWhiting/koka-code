fun show(m: maybe<a>, ?show: a -> e string): e string
  match m
    Just(m') -> "Just(" ++ show(m') ++ ")"
    Nothing -> "Nothing"

fun show(l: list<a>, ?show: a -> e string): e string
  show-list(l, show)

fun (==)(m1: maybe<a>, m2: maybe<a>, ?(==): (a, a) -> e bool): e bool
  match (m1, m2)
    (Just(m1'), Just(m2')) -> m1' == m2'
    (Nothing, Nothing) -> True
    _ -> False

fun (==)(l1: list<a>, l2: list<a>, ?eqA: (a, a) -> e bool = (==)): e bool
  match (l1, l2)
    (Cons(x1, xs1), Cons(x2, xs2)) -> eqA(x1,x2) && (==)(xs1, xs2, eqA)
    (Nil, Nil) -> True
    (_, _) -> False
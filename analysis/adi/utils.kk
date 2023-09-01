
fun (==)(l1: list<a>, l2: list<a>, eq: (a, a) -> e bool): e bool
  match (l1, l2)
    (Nil, Nil) -> True
    (Cons(x1, p1), Cons(x2, p2)) -> eq(x1, x2) && (==)(p1, p2, eq)
    _ -> False

fun (==)(m1: maybe<a>, m2: maybe<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (m1, m2)
    (Just(a1), Just(a2)) -> eqA(a1, a2)
    (Nothing, Nothing) -> True
    _ -> False

fun show(m: maybe<a>, showA: (a) -> e string): e string
  match m
    Just(a) -> showA(a)
    Nothing -> "⊥"

fun show(s: list<(string, a)>, showA: (a) -> e string): e string
  s.show-list(fn(t) t.show-tuple(show, showA))

fun fix3(a, b, c)
  fn(x)
    a(fix3(a, b, c), fix3(a, b, c), fix3(a, b, c))(x)

fun fix(f)
  fn(x)
    f(fix(f))(x)
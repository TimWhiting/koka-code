
fun (==)(l1: list<a>, l2: list<a>, eq: (a, a) -> e bool, showA: (a) -> e string): e bool
  with traceEq(l1, l2, fn(m:some<a> list<a>) m.show-list(showA))
  match (l1, l2)
    (Nil, Nil) -> True
    (Cons(x1, p1), Cons(x2, p2)) -> eq(x1, x2) && (==)(p1, p2, eq, showA)
    _ -> False

fun (==)(m1: maybe<a>, m2: maybe<a>, eqA: (a, a) -> e bool, showA: (a) -> e string): e bool
  with traceEq(m1, m2, fn(m:some<a> maybe<a>) m.show(showA))
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

fun fix(f: ((a -> <div|e> b) -> (a -> <div|e> b))): <div|e> (a -> <div|e> b)
  fn(x)
    f(fix(f))(x)

fun traceEq(a:a, b:a, showA: (a) -> e string, eqA: () -> e bool): e bool
  val v = eqA()
  if !v && showA(a) == showA(b) then
      trace("traceEq\n\t" ++ a.showA ++ "\n\t" ++ b.showA ++ "\n\t= " ++ v.show)
  v
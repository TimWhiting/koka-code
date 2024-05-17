
fun show(m: maybe<a>, showA: (a) -> e string): e string
  match m
    Just(a) -> showA(a)
    Nothing -> "⊥"

fun fix3(a, b, c)
  fn(x)
    a(fix3(a, b, c), fix3(a, b, c), fix3(a, b, c))(x)

fun fix(f: ((a -> <div|e> b) -> (a -> <div|e> b))): <div|e> (a -> <div|e> b)
  fn(x)
    f(fix(f))(x)

fun traceEq(a:a, b:a, eqA: () -> e bool, ?a/show: (a) -> e string): e bool
  val v = eqA()
  if !v && a.show == b.show then
      trace("traceEq\n\t" ++ a.show ++ "\n\t" ++ b.show ++ "\n\t= " ++ v.show)
  v
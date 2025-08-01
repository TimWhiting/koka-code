
fun fix3(a, b, c)
  fn(x)
    a(fix3(a, b, c), fix3(a, b, c), fix3(a, b, c))(x)

fun fix(f: ((a -> <div|e> b) -> (a -> <div|e> b))): <div|e> (a -> <div|e> b)
  fn(x)
    f(fix(f))(x)

fun traceEq(a:a, b:a, ?(==): (a, a) -> e bool, ?a/show: (a) -> e string): e bool
  val v = a == b
  if !v && a.show == b.show then
      trace("traceEq\n\t" ++ a.show ++ "\n\t" ++ b.show ++ "\n\t= " ++ v.show)
  v
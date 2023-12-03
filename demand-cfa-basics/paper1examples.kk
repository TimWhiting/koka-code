fun fold(f, g, n, a)
  if n == 0 then a
  else
    fold(f, g, f(n), g(f, n, a))

fun h(f, x, b)
  x

fun main()
  fold(fn(x) x - 1, h, 42, 1)
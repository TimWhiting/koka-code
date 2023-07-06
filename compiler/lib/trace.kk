import compiler/lib/printer

fun trace(s: string, a: a): a
  ctrace(DarkGray, s, a)

fun ctrace(c: color, message: string, a: a): a
  with unsafe-total
  with ansiPrinter
  message.ansiWithColor(c)
  a

fun traceId(s: string): string
  trace(s, s)

fun traceEq(s: string, a: a, showa: (a) -> string): a
  trace(s ++ " = " ++ a.showa, a)

// fun main()
//   ctrace(Red, "Hello, world!", 0).println
//   trace("Hi", 0).println
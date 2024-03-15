import std/core/unsafe
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

// fun example-trace()
//   ctrace(Red, "Hello, world!", 0)
//   trace("Hi", 0)
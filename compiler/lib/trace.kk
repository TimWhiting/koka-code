import std/core/unsafe
import compiler/lib/printer

fun color/trace(s: string, a: a, ?kk-file-line: string): a
  ctrace(DarkGray, s, a)

fun unit/trace(s: string, ?kk-file-line: string): ()
  trace(s, ())

fun trace-id(s: string, ?kk-file-line: string): string
  trace(s, s)
  
fun unit/trace-show(a: a, ?show: a -> e string, ?kk-file-line: string): e ()
  color/trace(a.show, ())

fun id/trace-show(a: a, ?show: a -> e string, ?kk-file-line: string): e a
  color/trace(a.show, a)

fun trace-eq(s: string, a: a, ?show: (a) -> string, ?kk-file-line: string): a
  trace(s ++ " = " ++ a.show, a)

fun ctrace(c: color, message: string, a: a, ?kk-file-line: string): a
  with unsafe-total
  with ansi-printer
  ansi-with-color(Blue)
    (kk-file-line ++ ": ").write()
  ansi-with-color(c)
    message.write-ln()
  a

// fun example-trace()
//   ctrace(Red, "Hello, world!", 0)
//   trace("Hi", 0)
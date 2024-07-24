//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 7/23/24: Commit b8074c2

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
  print-colored(?kk-file-line ++ ": ", Blue)
  println-colored(message, c)
  a

fun example-trace()
  ctrace(Red, "Hello, world!", 0)
  trace("Hi", 0)
import compiler/syntax/highlight
import compiler/common/color-scheme
import compiler/lib/printer
import std/os/path
import std/os/file

fun main(): <pure,console,fsys> ()
  with color-scheme-default
  with ansi-printer
  val p = "testcompiler/syntax/highlight.kk".path
  highlight-print(p, 0, read-text-file(p))
  "Hello".println-colored(Red)
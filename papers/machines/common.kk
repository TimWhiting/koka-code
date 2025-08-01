import papers/syntax/common
import std/data/linearset
effect malloc
  fun alloc(v: identifier): addr
effect salloc<s>
  fun salloc(s: s): addr
alias addr = int
alias time = int
effect abstraction
  ctl each(a: list<a>): a
effect tick<a>
  fun tick(a: a): int
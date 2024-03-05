import papers/syntax/common

effect malloc
  fun alloc(v: variable): addr
alias addr = int

effect abstraction
  ctl each(a: list<a>): a
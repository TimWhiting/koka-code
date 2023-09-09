fun fix(f: combinatorE<d,c,e>): div (d -> <div|e> c)
  f(fix(f))

fun fixC(f: combinatorE<d,c,e>, comb: combinatorE<d,c,e>): combE<d,c,e>
  fix(fn(fixed) comb(f(fixed)))

alias combinatorE<d,c,e> = (d -> <div|e> c) -> (d -> <div|e> c)
alias combinator<d,c> = some<e> (d -> <div|e> c) -> (d -> <div|e> c)
alias comb<d,c> = some<e> (d -> <div|e> c)
alias combE<d,c,e> = (d -> <div|e> c)

fun constComb(c)
  fn(a)
    c

fun filter(pred: (d -> bool), comb: combinator<d,c>): combinator<d,c>
  fn (f)
    fn (d)
      if pred(d) then
        comb(f)(d)
      else
        f(d)

fun unwind(steps: int, comb)
  fn (f: combE<d, c, e>): combE<d, c, e>
    fn (d: d): <div,local<h>|e> c
      f.repeat(steps)(d)
      comb(f)(d)

fun repeat(f: (a) -> e a, steps: int): (a -> e a)
  
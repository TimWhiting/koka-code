effect state<i,o,a,d>
  fun getAll(): a
  fun setAll(a: a): ()
  fun getIn(d: d): i
  fun setIn(d: d, i: i): ()
  fun getOut(d: d): o
  fun setOut(d: d, o: o): ()
  fun joinIn(d: d): i
  fun widenIn(d: d): i
  fun joinOut(d: d): o
  fun widenOut(d: d): o

fun fix(f: combinatorE<d,c,e>): div (d -> <div|e> c)
  f(fix(f))

fun fixC(f: combinatorE<d,c,e>, comb: combinatorE<d,c,e>): div combE<d,c,e>
  fix(fn(fixed) comb(f(fixed)))

alias combinatorE<d,c,e> = (d -> <div|e> c) -> (d -> <div|e> c)
alias combinator<d,c> = some<e> (d -> <div|e> c) -> (d -> <div|e> c)
alias comb<d,c> = some<e> (d -> <div|e> c)
alias combE<d,c,e> = (d -> <div|e> c)

fun constComb(c)
  fn(f)
    c

fun filter<d,c>(pred: (d -> bool), comb: combinator<d,c>): combinator<d,c>
  fn (f)
    fn (d)
      if pred(d) then
        comb(f)(d)
      else
        f(d)

fun unwind(steps: int, comb: forall<d,c> combinator<d,c>)
  fn (f: some<e,d,c> combE<d,c,e>)
    fn (a: some<d> d)
      val res = f.repeat(steps - 1)(a)
      comb(f)(res)

fun repeat(f: comb<d,c>, steps: int): comb<d,c>
  fn (a)
    f.repeat((steps - 1).unsafe-decreasing)(a)

fun dispatch<d,c,e>(choose: combE<d, int, e>, combs: list<combinatorE<d,c,e>>): combinatorE<d,c,e>
  fn(f:some<d,c,e> combE<d,c,e>)
    fn(a: some<d> d)
      val i = choose(a)
      match combs[i]
        Just(c) -> c(f)(a)
        Nothing -> f(a)

fun conditional(cond: combE<d,bool,e>, ifTrue: combinatorE<d,c,e>, ifFalse: combinatorE<d,c,e>): combinatorE<d,c,e>
  fn(f)
    fn(a)
      if cond(a) then
        ifTrue(f)(a)
      else
        ifFalse(f)(a)

struct sensitivity<d,c>
  emptyCtx: c
  switchCall: some<e> (d) -> e bool
  apply: some<e> (d) -> e c

fun product(s1: sensitivity<d,c1>, s2: sensitivity<d,c2>): sensitivity<d,(c1,c2)>
  val empty = (s1.emptyCtx, s2.emptyCtx)
  Sensitivity(empty, fn (d) (s1.switchCall)(d) || (s2.switchCall)(d), fn (d) ((s1.apply)(d), (s2.apply)(d)))

fun (&&)(s1: sensitivity<d,c1>, s2: sensitivity<d,c2>): sensitivity<d,(c1,c2)>
  product(s1, s2)

fun contextual(contexts: sensitivity<d,c>, contextFree: combinator<d,c> -> combinator<d,c>, contextSensitive: combinatorE<d,c,e> -> combinator<d,c,e>):
  fn(f) 
    cFix(fixpointAlgorithm(contexts, contextFree, contextSensitive))
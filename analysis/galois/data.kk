
struct monad<v,a,k,e>
  unit: v -> e a
  bind: (a, (v) -> e a) -> e a
  sigma-lookup: (k) -> e a
  sigma-extend: (k, v) -> e a

struct lattice<a,e::E>
  bottom: a
  union: (a, a) -> e a
  eq: (a, a) -> e bool

type evalue
  Clos(l: expr, rho: list<(string, string)>)
  CompileError(s: string)
  Dummy

type expr
  Symbol(x: string)
  App(e1: expr, e2: expr)
  Lam(x: string, e: expr)

fun expr/(==)(e1: expr, e2: expr): div bool
  match (e1, e2)
    (Symbol(x1), Symbol(x2)) -> x1 == x2
    (App(e11, e12), App(e21, e22)) -> e11 == e21 && e12 == e22
    (Lam(x1, e11), Lam(x2, e22)) -> x1 == x2 && e11 == e22
    _ -> False

fun ev/(==)(v1: evalue, v2: evalue): div bool
  match (v1, v2)
    (Clos(l1, rho1), Clos(l2, rho2)) -> l1 == l2 && rho1 == rho2
    (CompileError(s1), CompileError(s2)) -> s1 == s2
    (Dummy, Dummy) -> True
    _ -> False

fun config/(==)(v1: config, v2: config): div bool
  val (e1, rho1) = v1
  val (e2, rho2) = v2
  e1 == e2 && rho1 == rho2

alias trho = list<(string, string)>
alias config = (expr, trho)
alias abvalue = list<evalue>
alias absstore = list<(string, abvalue)>
alias mfi = some<e> (abvalue, absstore, absstore) -> e (abvalue, absstore, absstore)

// alias tinj<x,c,e> = x -> e c
alias tsing<c,r,s,e> = (c,r) -> e s
alias tlook<s,c,r,e> = (s,c) -> e r
alias teq<a,e> = (a,a) -> e bool
alias tseen<c,s,r,e> = (c) -> e ((list<c>, s) -> e (r, s));
// alias tseen<c,p,s,e> = c -> e (p, s)
// alias talpha<p,q,s,c,v,m,e> = (tseen<c,p,s,e>, (q, s)) -> (v -> e m)
// alias tgamma<v,m,p,q,s,c,e> = ((v -> e m) -> e tseen<c,p,s,e>) -> e (q, s)
// alias tstrip<s,c,p,q,e> = (tseen<c,p,s,e> -> e (q, s)) -> e (c -> e (s -> e s))

struct analysis<c,s,r,m,b,e,x>
  lat : lattice<s,e>
  m : b
  inj : (x) -> e c
  singleton : tsing<c,r,s,e> 
  lookup : tlook<s,c,r,e>
  alpha : tseen<c,s,r,e> -> e m
  gamma : (m) -> e tseen<c,s,r,e>
  strip : tseen<c,s,r,e> -> e ((c) -> e ((s) -> e s));


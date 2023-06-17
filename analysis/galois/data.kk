
struct monad<v,a,k,e>
  unit: v -> e a
  bind: (a, (v) -> e a) -> e a
  sigma-lookup: (k) -> e a
  sigma-extend: (k, v) -> e a

alias lattice<a,e::E> = (a, (a, a) -> e a, (a, a) -> e bool)

fun bottom(a: lattice<a,e>): a
  a.fst

fun union(a: lattice<a,e>): ((a, a) -> e a)
  a.snd

fun eq(a: lattice<a,e>): ((a, a) -> e bool)
  a.thd

type evalue
  Clos(l: expr, rho: list<(string, string)>)
  CompileError(s: string)
  Dummy

type expr
  Symbol(x: string)
  App(e1: expr, e2: expr)
  Lam(x: string, e: expr)

fun (==)(e1: expr, e2: expr): bool
  match (e1, e2)
    (Symbol(x1), Symbol(x2)) -> x1 == x2
    (App(e11, e12), App(e21, e22)) -> e11.unsafe-decreasing == e21.unsafe-decreasing && e12.unsafe-decreasing == e22.unsafe-decreasing
    (Lam(x1, e11), Lam(x2, e22)) -> x1 == x2 && e11.unsafe-decreasing == e22.unsafe-decreasing
    _ -> False

fun eq-expr(v1: expr, v2: expr): e bool
  v1 == v2

fun eq-string(v1: string, v2: string): bool
  v1 == v2
fun eq-value(v1: evalue, v2: evalue): bool
  v1 == v2

fun eq-rho(l1: list<(string, string)>, l2: list<(string, string)>): bool
  list-eq(tup-eq(eq-string, eq-string))(l1, l2)

fun (==)(v1: evalue, v2: evalue): bool
  match (v1, v2)
    (Clos(l1, rho1), Clos(l2, rho2)) -> l1 == l2 && eq-rho(rho1, rho2)
    (CompileError(s1), CompileError(s2)) -> s1 == s2
    (Dummy, Dummy) -> True
    _ -> False

fun tup-eq(eqA: (a, a) -> e bool, eqB: (b, b) -> e bool): (((a, b), (a, b)) -> e bool)
  fn(a, b)
    eqA(a.fst, b.fst) && eqB(a.snd, b.snd)

fun list-eq(eq: (a, a) -> e bool): ((list<a>, list<a>) -> e bool)
  fn(l1, l2)
    match (l1, l2)
      (Cons(x, xs), Cons(y, ys)) -> if eq(x, y) then list-eq(eq.unsafe-decreasing)(xs.unsafe-decreasing, ys.unsafe-decreasing) else False
      (Nil, Nil) -> True
      _ -> False


val configkeyeq = tup-eq(eq-value, eq-rho)

fun config-eq(v1: config, v2: config): bool
  val (e1, rho1) = v1
  val (e2, rho2) = v2
  e1 == e2 && eq-rho(rho1, rho2)

fun absstore-eq(l1: absstore, l2: absstore): bool
  list-eq(tup-eq(eq-string, list-eq(eq-value)))(l1, l2)

fun tup3-eq(eq1: (a, a) -> e bool, eq2: (b, b) -> e bool, eq3: (c, c) -> e bool): (((a, b, c), (a, b,c)) -> e bool)
  fn(t1, t2)
    val (a, b, c) = t1
    val (a', b', c') = t2
    eq1(a, a') && eq2(b, b') && eq3(c, c')



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


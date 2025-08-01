import papers/syntax/common

struct call
  funct: atomicExpr
  args: list<atomicExpr>

type atomicExpr
  Var(v: variable)
  Lam(l: lambda)

struct lambda
  vars: list<variable>
  body: call

fun lambda/(==)(l1: lambda, l2: lambda): div bool
  l1.vars == l2.vars && l1.body == l2.body

fun atomicExpr/(==)(e1: atomicExpr, e2: atomicExpr): div bool
  match (e1, e2)
    (Var(v1), Var(v2)) -> v1 == v2
    (Lam(l1), Lam(l2)) -> l1 == l2
    (_, _) -> False

fun call/(==)(c1: call, c2: call): div bool
  c1.funct == c2.funct && c1.args == c2.args
import papers/syntax/cps
import papers/syntax/common
import papers/machines/common
import papers/machines/aces

type count
  Zero
  One
  Many

fun count/(+)(x: count, y: count): count
  match (x,y)
    (Zero, _) -> y
    (_, Zero) -> x
    (_, _) -> Many
val count/join = count/(+)

alias counts = list<(addr, count)>

fun suAtomicEval(at: atomicExpr, ?env: aenv, ?store: astore): <pure,abstraction> aclos
  match at
    Var(x) -> each(store.lookup(env.lookup(x)))
    Lam(l) -> Aclos(l, env)

fun suG(at: atomicExpr, clo: aclos, ?env: aenv, ?store: astore, ?counts: counts): <pure,abstraction> astore
  match at
    Var(x) -> if !counts.lookup(env.lookup(x)).is-many then store.set(env.lookup(x), [clo]) else store
    Lam -> store

fun suEval(e: call, env: aenv, store: astore, counts: counts): <pure,malloc,abstraction> aclos
  val Aclos(lam, p') = suAtomicEval(e.funct)
  val addrs = lam.vars.map(alloc)
  val p'' =  p'.extend(lam.vars.zip(addrs))
  val s' = suG(e.funct, Aclos(lam, p'))
  val s''' = store.join(addrs.zip(e.args.map(fn(a) a.suAtomicEval)), ?b/(==) = (==))
  val counts' = counts.join(addrs.map(fn(a) (a, One)))
  suEval(lam.body, p'', s', counts')
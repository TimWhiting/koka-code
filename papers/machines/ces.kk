import papers/syntax/cps
import papers/syntax/common
import papers/machines/common

alias sigma = (call, env, store)
alias env = linearMap<variable,addr>
alias store = linearMap<addr,clos>
alias clos = (lambda,env)


fun atomicEval(at: atomicExpr, ?env: env, ?store: store): pure clos
  match at
    Var(x) -> store.lookup(env.lookup(x).unjust).unjust
    Lam(l) -> (l, env)

fun eval(e: call, env: env, store: store): <pure,malloc> clos
  val (lam, p') = atomicEval(e.funct)
  val addrs = lam.vars.map(alloc)
  val p'' =  p'.add-all(lam.vars.zip(addrs))
  val s' = store.add-all(addrs.zip(e.args.map(fn(a) a.atomicEval)))
  eval(lam.body, p'', s')

import papers/syntax/cps
import papers/syntax/common
import papers/machines/common

alias asigma = (atomicExpr, aenv, astore)
alias aenv = linearMap<variable,addr>
alias astore = linearMap<addr,linearSet<aclos>>;
value struct aclos
  alam: lambda
  aenv: aenv

fun (==)(a: aclos, b: aclos): div bool
  a.alam == b.alam && a.aenv == b.aenv

fun aatomicEval(at: atomicExpr, ?env: aenv, ?store: astore): <pure,abstraction> aclos
  match at
    Var(x) -> each(store.lookup(env.lookup(x).unjust).unjust.list)
    Lam(l) -> Aclos(l, env)

fun aeval(e: call, env: aenv, store: astore): <pure,malloc,abstraction> aclos
  val Aclos(lam, p') = aatomicEval(e.funct)
  val addrs = lam.vars.map(alloc)
  val p'' =  p' + lam.vars.zip(addrs)
  val s' = store.join(LinearMap(addrs.zip(e.args.map(fn(a) a.aatomicEval))))
  aeval(lam.body, p'', s')

import papers/syntax/cps
import papers/syntax/common
import papers/machines/common

alias asigma = (atomicExpr, aenv, astore)
alias aenv = list<(variable,addr)>
alias astore = list<(addr,list<aclos>)>;
value struct aclos
  alam: lambda
  aenv: aenv

fun aclos/(==)(a: aclos, b: aclos): pure bool
  a.alam == b.alam && a.aenv == b.aenv

fun aenv/(==)(a: aenv, b: aenv): pure bool
  a.length == b.length && a.all(fn((x,y)) b.lookup(x) == y)

fun aatomicEval(at: atomicExpr, ?env: aenv, ?store: astore): <pure,abstraction> aclos
  match at
    Var(x) -> each(store.lookup(env.lookup(x)))
    Lam(l) -> Aclos(l, env)

fun aeval(e: call, env: aenv, store: astore): <pure,malloc,abstraction> aclos
  val Aclos(lam, p') = aatomicEval(e.funct)
  val addrs = lam.vars.map(alloc)
  val p'' =  p'.extend(lam.vars.zip(addrs))
  val s' = store.join(addrs.zip(e.args.map(fn(a) a.aatomicEval)), ?b/(==) = (==))
  aeval(lam.body, p'', s')

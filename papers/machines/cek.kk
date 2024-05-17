import papers/syntax/common

alias state = (expr, env, kont)
alias env = list<(identifier,evalue)>
alias kont = list<frame>

rec type frame
  AppL(e: expr, env: env)
  AppR(v: evalue)
rec type evalue
  Clos(l: lambda, env: env)
rec type lambda
  Lam(x: identifier, e: expr)
rec type expr
  Var(x: identifier)
  App(e1: expr, e2: expr)
  Lambda(l: lambda)

fun expr/show(e: expr): div string
  match e
    Var(x) -> x
    App(e1, e2) -> e1.show ++ " " ++ e2.show
    Lambda(l) -> "λ" ++ l.show

fun lambda/show(l: lambda): div string
  match l
    Lam(x, e) -> x ++ "." ++ e.show


fun state/next(s: state)
  match s
    (Var(id), env, kont) ->
      val Clos(l, env') = env.lookup(id).unjust
      (Lambda(l), env', kont).next()
    (App(e1, e2), env, kont) ->
      (e1, env, Cons(AppL(e2, env), kont)).next()
    (Lambda(l), env, Cons(AppL(e, env'), kont)) -> 
      (e, env', Cons(AppR(Clos(l, env)), kont)).next()
    (Lambda(l), env, Cons(AppR(Clos(Lam(id, e), env')), kont)) ->
      (e, env'.set(id, Clos(l, env)), kont).next()
    (e, env, k) -> (e, env, k)

fun expr/eval(e: expr): <pure,console> ()
  val res = (e, [], []).next()
  match res
    (l, _, _) -> l.show.println

fun tests(): <pure, console> ()
  Lambda(Lam("x", Var("x"))).eval



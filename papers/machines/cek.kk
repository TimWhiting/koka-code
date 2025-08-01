import papers/syntax/common
import std/core/undiv

type state
  Eval(e: expr, p: env, k: kont)
  Continue(k: kont, v: evalue)
  Ans(v: evalue)
alias env = linearMap<identifier,evalue>
alias kont = list<frame>

div type frame
  AppL(e: expr, env: env)
  AppR(v: evalue)
div type evalue
  Clos(l: lambda, env: env)
div type lambda
  Lam(x: identifier, e: expr)
div type expr
  Var(x: identifier)
  App(e1: expr, e2: expr)
  Lambda(l: lambda)

fun state/eval(s: state): pure state 
  match s
    Eval(Var(id), env, kont) ->
      Continue(kont, env.lookup(id).unjust).eval()
    Eval(App(e1, e2), env, kont) ->
      Eval(e1, env, Cons(AppL(e2, env), kont)).eval()
    Eval(Lambda(l), env, kont) ->
      Continue(kont, Clos(l, env ~! fv(l))).eval()
    Continue(Cons(AppL(e, env'), kont), Clos(l, env)) -> 
      Eval(e, env', Cons(AppR(Clos(l, env)), kont)).eval()
    Continue(Cons(AppR(Clos(Lam(id, e), env')), kont), Clos(l, env)) ->
      Eval(e, env'.set(id, Clos(l, env)), kont).eval()
    Continue([], v) -> Ans(v)


fun expr/eval(e: expr): <pure,console> ()
  val res = Eval(e, LinearMap([]), []).eval()
  res.show.println

fun tests(): <pure, console> ()
  Lambda(Lam("x", Var("x"))).eval


fun lam/fv(l: lambda): div linearSet<identifier>
  match l
    Lam(x, e) -> fv(e) - x

fun expr/fv(e: expr): div linearSet<identifier>
  match e
    Var(x) -> [x].LinearSet
    App(e1, e2) -> e1.fv.union(e2.fv)
    Lambda(l) -> fv(l)

fun expr/show(e: expr): div string
  match e
    Var(x) -> x
    App(e1, e2) -> e1.show ++ " " ++ e2.show
    Lambda(l) -> l.show

fun lambda/show(l: lambda): div string
  match l
    Lam(x, e) -> "λ" ++ x ++ "." ++ e.show

fun result/show(r: evalue): div string
  match r
    Clos(l, env) -> l.show ++ " " ++ env.show-env

fun show-env(e: env): div string
  "<env>[" ++ e.list.map(fn((x,v)) x ++ " -> " ++ v.show).join(", ") ++ "]"

fun frame/show(f: frame): div string
  match f
    AppL(e, env) -> "AppL(" ++ e.show ++ ", " ++ env.show-env ++ ")"
    AppR(v) -> "AppR(" ++ v.result/show ++ ")"

fun state/show(s: state): div string
  match s
    Eval(e, env, kont) -> e.show ++ " " ++ env.show-env ++ " " ++ kont.show()
    Continue(k, v) -> k.show ++ " " ++ v.show
    Ans(v) -> v.show

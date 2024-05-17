import papers/syntax/common
import papers/machines/common

struct state
  expr: expr
  rho: env
  store: store
  kont: kont
  t: time

alias env = linearMap<identifier,addr>
alias store = linearMap<addr, linearSet<storeable>>
alias storeable = either<kont, evalue>

fun expr/(==)(e1: expr, e2: expr): div bool
  match (e1, e2)
    (Var(x1), Var(x2)) -> x1 == x2
    (App(e1, e2), App(e1', e2')) -> e1 == e1' && e2 == e2'
    (Lambda(l1), Lambda(l2)) -> l1 == l2
    (_, _) -> False

fun lambda/(==)(l1: lambda, l2: lambda): div bool
  match (l1, l2)
    (Lam(x1, e1), Lam(x2, e2)) -> x1 == x2 && e1 == e2

fun evalue/(==)(v1: evalue, v2: evalue): div bool
  match (v1, v2)
    (Clos(l1, env1), Clos(l2, env2)) -> l1 == l2 && env1 == env2

fun kont/(==)(k1: kont, k2: kont): div bool
  match (k1, k2)
    (Epsilon, Epsilon) -> True
    (Frame(f1, a1), Frame(f2, a2)) -> f1 == f2 && a1 == a2
    (_, _) -> False

fun frame/(==)(f1: frame, f2: frame): div bool
  match (f1, f2)
    (AppL(e1, env1), AppL(e2, env2)) -> e1 == e2 && env1 == env2
    (AppR(v1), AppR(v2)) -> v1 == v2
    (_, _) -> False

fun storeable/(==)(s1: storeable, s2: storeable): div bool
  match (s1, s2)
    (Left(k1), Left(k2)) -> k1 == k2
    (Right(v1), Right(v2)) -> v1 == v2
    (_, _) -> False

rec type kont
  Epsilon
  Frame(f: frame, addr: addr)

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

fun state/eval(s: state): <pure,abstraction,salloc<state>,tick<state>> state
  val u = tick(s)
  match s
    State(Var(x), env, st, k, _) ->
      val Right(Clos(l, env')) = each(st.lookup(env.lookup(x).unjust).unjust)
      State(Lambda(l), env', st, k, u)
    State(App(e0, e1), env, st, k, _) ->
      val a = salloc(s)
      State(e0, env, st.set/join(a, Left(k)), Frame(AppL(e1, env), a), u)
    State(Lambda(l), p, st, Frame(AppL(e, p'), b), _) ->
      State(e, p', st, Frame(AppR(Clos(l, p)), b), u)
    State(Lambda(l), po, st, Frame(AppR(Clos(Lam(x, e), p)), b), _) ->
      val a = salloc(s)
      val Left(k) = each(st.lookup(b).unjust)
      State(e, p.set(x, a), st.set/join(a, Right(Clos(l, po))), k, u)
    _ -> s

fun expr/eval(e: expr): <pure,console> ()
  var x := 0
  var t := 0
  with handler
    fun tick(s)
      t := t + 1
      t
  with handler
    fun salloc(z)
      x := x + 1
      x
  val res = 
    with handler
      ctl each(xs)
        xs.map(resume).concat()
      return (res) 
        [res]
    State(e, [], [], Epsilon, 0).eval()
  res.map(fn(s) s.expr.show).join("\n").println

fun tests(): <pure, console> ()
  Lambda(Lam("x", Var("x"))).eval





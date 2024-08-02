import papers/syntax/common
import papers/machines/common
import std/core-extras

type state
  Eval(expr: expr, rho: env, store: store, k: kont)
  Continue(k: kont, value: evalue, store: store)
  Ans(value: evalue)

alias env = linearMap<identifier,addr>
struct storeables { vs: linearSet<storeable> }
alias store = linearMap<addr, storeables>
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

fun storeable/(==)(s1: storeable, s2: storeable): div bool
  match (s1, s2)
    (Left(k1), Left(k2)) -> listdiv/(==)(k1, k2)
    (Right(v1), Right(v2)) -> v1 == v2
    (_, _) -> False

fun frame/(==)(f1: frame, f2: frame): div bool
  match (f1, f2)
    (AppL(e1, env1), AppL(e2, env2)) -> e1 == e2 && env1 == env2
    (AppR(v1), AppR(v2)) -> v1 == v2
    (_, _) -> False

fun storeables/(==)(s1: storeables, s2: storeables): div bool
  linearset/(==)(s1.vs, s2.vs)

fun state/(==)(s1: state, s2: state): div bool
  match (s1, s2)
    (Eval(e1, rho1, st1, k1), Eval(e2, rho2, st2, k2)) -> e1 == e2 && rho1 == rho2 && st1 == st2 && listdiv/(==)(k1, k2)
    (Continue(k1, v1, st1), Continue(k2, v2, st2)) -> listdiv/(==)(k1, k2) && v1 == v2 && st1 == st2
    (Ans(v1), Ans(v2)) -> v1 == v2
    (_, _) -> False

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

fun storeable/show(s: storeable): div string
  match s
    Left(k) -> k.list/show
    Right(v) -> v.show

fun storeables/show(s: storeables): div string
  s.vs.show

fun evalue/show(v: evalue): div string
  match v
    Clos(l, env) -> l.show ++ " " ++ env.show

fun frame/show(f: frame): div string
  match f
    AppL(e, env) -> "AppL(" ++ e.show ++ ", " ++ env.show ++ ")"
    AppR(v) -> "AppR(" ++ v.show ++ ")"

fun state/show(s0: state): div string
  match s0
    Eval(e, rho, st, k) -> "Eval(" ++ e.show ++ ", " ++ rho.show ++ ", " ++ st.show ++ ", " ++ k.list/show ++ ")"
    Continue(k, v, st) -> "Continue(" ++ k.list/show ++ ", " ++ v.show ++ ", " ++ st.show ++ ")"
    Ans(v) -> "Ans(" ++ v.show ++ ")"

fun join(s: storeables, st: storeable) 
  Storeables(s.vs + st)

fun empty(): storeables
  Storeables(LinearSet([]))

tail fun state/eval(s: state): <pure,abstraction,cache,salloc<state>> state
  with memo(s)
  match s
    Eval(Var(x), env, st, k) ->
      val Right(v) = each(st.lookup(env.lookup(x).unjust).unjust.vs.list)
      Continue(k, v, st)
    Eval(App(e0, e1), env, st, k) ->
      Eval(e0, env ~! e0.fv, st, Cons(AppL(e1, env ~! e1.fv), k))
    Eval(Lambda(l), p, st, k) ->
      Continue(k, Clos(l, p ~! l.e.fv), st)
    Continue(Nil, v, _) -> Ans(v)
    Continue(Cons(AppL(e, p'), rst), v, st) -> 
      Eval(e, p', st, Cons(AppR(v), rst))
    Continue(Cons(AppR(Clos(Lam(x, e), p)), rst), v, st) ->
      val a = salloc(s)
      Eval(e, (p.set(x, a)) ~! e.fv, st.join(a, Right(v)), rst)
    Continue(_, v, _) -> 
      v.show.trace
      Ans(v)

fun memo(s: state, s': () -> <cache,pure,abstraction,salloc<state>|e> state): <cache,pure,abstraction,salloc<state>|e> state
  val res = get-cache(s)
  match res
    Nothing ->
      val r = s'()
      add-cache(s, r)
      r.eval()
    Just() -> each([])

effect cache
  fun get-cache(s: state): maybe<linearSet<state>>
  fun add-cache(s: state, s': state): ()

fun expr/eval(e: expr): <pure,console> ()
  var x := 0
  var cache: linearMap<state, linearSet<state>> := LinearMap([])
  var cacheids: linearMap<(env,lambda), int> := LinearMap([])
  with handler
    fun get-cache(s: state)
      cache.lookup(s)
    fun add-cache(s: state, s': state)
      val ss = cache.lookup(s).default(LinearSet([]))
      cache := cache.set(s, member/(+)(ss, s'))
  with handler
    fun salloc(s)
      match s
        Continue(Cons(AppR(Clos(exp, p)), _), _, _) ->
          match cacheids.map/lookup((p, exp), ?(==)=fn(p1,p2) tuple2div/(==)(p1,p2))
            Nothing ->
              cacheids := cacheids.linearmap/set((p, exp),x, ?(==)=fn(p1,p2) tuple2div/(==)(p1,p2))
              x := x + 1
              x
            Just(y) -> y
  val res =
    with handler
      ctl each(xs)
        xs.map(resume).concat()
      return (res)
        [res]
    Eval(e, LinearMap([]), LinearMap([]), []).eval()
  if res.length == 0 then
    "Bottom".println
  else
    res.map(fn(Ans(Clos(e1, _))) e1.show).join("\n").println

fun tests(): <pure, console> ()
  App(Lambda(Lam("x", App(Var("x"), Var("x")))), Lambda(Lam("y", App(Var("y"), Var("y"))))).eval

fun lam/fv(l: lambda): div linearSet<identifier>
  match l
    Lam(x, e) -> fv(e) - x

fun expr/fv(e: expr): div linearSet<identifier>
  match e
    Var(x) -> LinearSet([x])
    App(e1, e2) -> e1.fv.union(e2.fv)
    Lambda(l) -> fv(l)
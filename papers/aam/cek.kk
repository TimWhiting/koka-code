import std/data/linearmap
import std/test

type expr
  Var(ident: string)
  App(f: expr, x: expr)
  Lam(l: lam)

fun expr/(==)(e1: expr, e2: expr): div bool
  match (e1, e2)
    (Var(x1), Var(x2)) -> x1 == x2
    (App(f1, x1), App(f2, x2)) -> f1 == f2 && x1 == x2
    (Lam(l1), Lam(l2)) -> l1 == l2
    _ -> False

fun expr/show(e: expr): div string
  match e
    Var(x) -> x
    App(f, x) -> "(" ++ show(f) ++ " " ++ show(x) ++ ")"
    Lam(l) -> l.show

type lam
  ELam(ident: string, body: expr)

fun lam/(==)(l1: lam, l2: lam): div bool
  l1.ident == l2.ident && l1.body == l2.body

fun lam/show(l: lam): div string
  match l
    ELam(id, bod) -> "(\\" ++ id ++ "." ++ show(bod) ++ ")"

alias evalue = lam;

reference struct env
  internal: linearMap<string, clos>;

// Automatically generated.
// Shows a string representation of the `env` type.
pub fun env/show(this : env) : div string
  match this
    Env(internal) -> "Env(internal: " ++ internal.show ++ ")"

fun env/(==)(rho1: env, rho2: env): div bool
  rho1.internal == rho2.internal

struct clos
  lam: lam
  rho: env

// Automatically generated.
// Shows a string representation of the `clos` type.
pub fun clos/show(this : clos) : div string
  match this
    Clos(lam, rho) -> "Clos(lam: " ++ lam.show ++ ", rho: " ++ rho.show ++ ")"

fun clos/(==)(c1: clos, c2: clos): div bool
  c1.lam == c2.lam && c1.rho == c2.rho

type kont
  Arg(e: expr, rho: env, k: kont)
  Fun(ev: evalue, rho: env, k: kont)
  Mt

// Automatically generated.
// Shows a string representation of the `kont` type.
pub fun kont/show(this : kont) : div string
  match this
    Arg(e, rho, k) -> "Arg(e: " ++ e.show ++ ", rho: " ++ rho.show ++ ", k: " ++ k.show ++ ")"
    Fun(ev, rho, k) -> "Fun(ev: " ++ ev.show ++ ", rho: " ++ rho.show ++ ", k: " ++ k.show ++ ")"
    Mt -> "Mt"

fun kont/(==)(k1: kont, k2: kont): div bool
  match (k1, k2)
    (Arg(e1, rho1, k1), Arg(e2, rho2, k2)) -> e1 == e2 && rho1 == rho2 && k1 == k2
    (Fun(v1, rho1, k1), Fun(v2, rho2, k2)) -> v1 == v2 && rho1 == rho2 && k1 == k2
    (Mt, Mt) -> True
    _ -> False

type state
  Eval(e: expr, rho: env, k: kont)
  Cont(v: evalue, rho: env, k: kont)

// Automatically generated.
// Shows a string representation of the `state` type.
pub fun state/show(this : state) : div string
  match this
    Eval(e, rho, k) -> "Eval(e: " ++ e.show ++ ", rho: " ++ rho.show ++ ", k: " ++ k.show ++ ")"
    Cont(v, rho, k) -> "Cont(v: " ++ v.show ++ ", rho: " ++ rho.show ++ ", k: " ++ k.show ++ ")"

fun inj(e: expr): state
  Eval(e, Env(LinearMap([])), Mt)
 
fun cek-eval(s: state): pure state
  match s
    Eval(Lam(l), rho, k) -> Cont(l, rho, k)
    Eval(Var(x), rho, k) -> 
      val Clos(v, rho') = rho.internal.get(x)
      Cont(v, rho', k)
    Eval(App(f, x), rho, k) -> Eval(f, rho, Arg(x, rho, k))
    Cont(v, rho, Arg(e, rho', k)) -> Eval(e, rho', Fun(v, rho, k))
    Cont(v, rho, Fun(ELam(id, bod), rho', k)) -> 
      Eval(bod, Env(rho'.internal.set(id, Clos(v, rho))), k)
    Cont(v, rho, Mt) -> Cont(v, rho, Mt)

fun run/eval(s: state): pure state
  match cek-eval(s)
    Cont(v, rho, Mt) -> Cont(v, rho, Mt)
    s' -> run/eval(s')

fun main()
  with run-tests
  test("cek-eval")
    expect(Mt)
      val s = App(Lam(ELam("x", Var("x"))), Lam(ELam("y", Var("y"))))
      trace(s.show)
      val s' = run/eval(s.inj)
      val Cont(v, _, k) = s'
      trace(v.show)
      k



pub value struct assoc<k,v>
  internal: list<(k,v)> 

pub fun map/(==)(l1: assoc<k,v>, l2: assoc<k,v>, ?key/(==): (k, k) -> e bool, ?value/(==): (v, v) -> e bool): e bool
  l1.internal.length == l2.internal.length && l1.internal.all fn(x) 
    match l2.internal.lookup(x.fst)
      Just(v') -> v' == x.snd
      Nothing -> False

pub fun map/show(l: assoc<k,v>, ?key/show: (k) -> e string, ?value/show: (v) -> e string): e string
  "{" ++ l.internal.map(fn((k,v)) k.show ++ ": " ++ v.show).join(",") ++ "}"

pub fun map/get(m: assoc<k,v>, k: k, ?(==): (k, k) -> <exn|e> bool, ?kk-file-line: string): <exn|e> v  
  m.internal.lookup(k).unjust

pub fun list/lookup(m: list<(k,v)>, k: k, ?(==): (k, k) -> e bool): e maybe<v>
  match m
    Cons((kk, vv), rst) -> if kk == k then Just(vv) else rst.lookup(k)
    Nil -> Nothing
  
pub fun list/set(l: list<(k,v)>, k: k, b: v, ?(==): (k, k) -> e bool): e list<(k,v)>
  match l
    Cons((kk, vv), rst) -> if k == kk then Cons((kk, b), rst) else Cons((kk, vv), rst.set(k, b))
    Nil -> Cons((k, b), Nil) 

/// Overwrite any existing key with value
pub fun set(m: assoc<k,v>, k: k, v: v, ?(==): (k, k) -> e bool): e assoc<k,v>
  Assoc(m.internal.set(k, v))

reference type expr
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

reference type lam
  ELam(ident: string, body: expr)

fun lam/(==)(l1: lam, l2: lam): div bool
  l1.ident == l2.ident && l1.body == l2.body

fun lam/show(l: lam): div string
  match l
    ELam(id, bod) -> "(\\" ++ id ++ "." ++ show(bod) ++ ")"

reference struct env
  internal: assoc<string, clos>;

// Automatically generated.
// Shows a string representation of the `env` type.
pub fun env/show(this : env) : div string
  match this
    Env(internal) -> "Env(internal: " ++ internal.show ++ ")"

fun env/(==)(rho1: env, rho2: env): div bool
  rho1.internal == rho2.internal

reference struct clos
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
  Fun(ev: clos, k: kont)
  Mt

// Automatically generated.
// Shows a string representation of the `kont` type.
pub fun kont/show(this : kont) : div string
  match this
    Arg(e, rho, k) -> "Arg(e: " ++ e.show ++ ", rho: " ++ rho.show ++ ", k: " ++ k.show ++ ")"
    Fun(ev, k) -> "Fun(ev: " ++ ev.show ++ ", k: " ++ k.show ++ ")"
    Mt -> "Mt"

reference type state
  Eval(e: expr, rho: env, k: kont)
  Cont(v: clos, k: kont)

// Automatically generated.
// Shows a string representation of the `state` type.
pub fun state/show(this : state) : div string
  match this
    Eval(e, rho, k) -> "Eval(e: " ++ e.show ++ ", rho: " ++ rho.show ++ ", k: " ++ k.show ++ ")"
    Cont(v, k) -> "Cont(v: " ++ v.show ++ ", k: " ++ k.show ++ ")"
 
fun cek-eval(s: state): pure state
  match s
    Eval(Lam(l), rho, k) -> Cont(Clos(l, rho), k)
    Eval(Var(x), rho, k) -> 
      trace("Var " ++ rho.show)
      val v = rho.internal.get(x)
      Cont(v, k)
    Eval(App(f, x), rho, k) -> Eval(f, rho, Arg(x, rho, k))
    Cont(v, Arg(e, rho', k)) -> Eval(e, rho', Fun(v, k))
    Cont(v, Fun(Clos(ELam(id, bod), rho'), k)) -> 
      trace("Here " ++ rho'.show)
      Eval(bod, Env(rho'.internal.set(id, v)), k)
    Cont(v, Mt) -> Cont(v, Mt)

fun run/eval(s: state): pure state
  match cek-eval(s)
    Cont(v, Mt) -> 
      trace("Done")
      Cont(v, Mt)
    s' -> 
      trace("Next")
      trace(s'.show)
      run/eval(s')

fun main()
  val s = App(Lam(ELam("x", Var("x"))), Lam(ELam("y", Var("y"))))
  trace(s.show)
  val s' = run/eval(Eval(s, Env(Assoc([])), Mt))
  trace("Done")


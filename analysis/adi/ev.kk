import analysis/cps/sexpr
import newstd/data/linearMap
import newstd/data/linearSet

type expr
  Num(i: int)
  If0(e0: expr, e1: expr, e2: expr)
  Op2(op: string, e0: expr, e1: expr)
  Id(x: string)
  Rec(x: string, e: expr)
  Lam(v: string, e: expr)
  App(e0: expr, e1: expr)

fun (==)(e1: expr, e2: expr): div bool
  match (e1, e2)
    (Num(i1), Num(i2)) -> i1 == i2
    (If0(e1, e2, e3), If0(e4, e5, e6)) -> e1 == e4 && e2 == e5 && e3 == e6
    (Op2(op1, e1, e2), Op2(op2, e3, e4)) -> op1 == op2 && e1 == e3 && e2 == e4
    (Id(x1), Id(x2)) -> x1 == x2
    (Rec(x1, e1), Rec(x2, e2)) -> x1 == x2 && e1 == e2
    (Lam(x1, e1), Lam(x2, e2)) -> x1 == x2 && e1 == e2
    (App(e1, e2), App(e3, e4)) -> e1 == e3 && e2 == e4
    _ -> False

fun subexprs(e: expr): list<expr>
  match e
    Num(_) -> [e]
    If0(e0, e1, e2) -> Cons(e, e0.subexprs ++ e1.subexprs ++ e2.subexprs)
    Op2(_, e0, e1) -> Cons(e, e0.subexprs ++ e1.subexprs)
    Id(_) -> [e]
    Rec(_, e0) -> Cons(e, e0.subexprs)
    Lam(_, e0) -> Cons(e, e0.subexprs)
    App(e0, e1) -> Cons(e, e0.subexprs ++ e1.subexprs)

alias env<a> = list<(string, a)>

type evalue<a>
  NumV(i: int)
  Clos(e: expr, p: env<a>)
  ErrorV

value type lattice<a>
  Top
  Bottom
  Elem(a: a)

alias abenv<a> = list<(string, a)>;

value struct abclos<a>
  e: expr
  p: abenv<a>;

struct abvalue<a>
  num: maybe<lattice<int>>
  clos: maybe<linearSet<abclos<a>>>;

fun (==)(e1: evalue<a>, e2: evalue<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (e1, e2)
    (NumV(i1), NumV(i2)) -> i1 == i2
    (Clos(e1, p1), Clos(e2, p2)) -> e1 == e2 && (==)(p1, p2, eqA)
    (ErrorV, ErrorV) -> True
    _ -> False

fun (==)(e1: env<a>, e2: env<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (e1, e2)
    (Nil, Nil) -> True
    (Cons((x1, a1), p1), Cons((x2, a2), p2)) -> x1 == x2 && eqA(a1, a2) && (==)(p1, p2, eqA)
    _ -> False

fun (==)(l1: lattice<a>, l2: lattice<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (l1, l2)
    (Top, Top) -> True
    (Bottom, Bottom) -> True
    (Elem(a1), Elem(a2)) -> eqA(a1, a2)
    _ -> False

fun (==)(c1: abclos<a>, c2: abclos<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  c1.e == c2.e && (==)(c1.p, c2.p, eqA)

fun (==)(m1: maybe<a>, m2: maybe<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (m1, m2)
    (Just(a1), Just(a2)) -> eqA(a1, a2)
    (Nothing, Nothing) -> True
    _ -> False

fun (==)(s1: linearSet<a>, s2: linearSet<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  s1.list.length == s2.list.length && s1.list.all(fn(a) s2.list.any(fn(b) eqA(a, b)))

fun (==)(v1: abvalue<a>, v2: abvalue<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  val numEq = (==)(v1.num, v2.num, fn(a1, a2) (==)(a1, a2, (==)))
  if !numEq then return False
  (==)(v1.clos, v2.clos, fn(a1, a2) (==)(a1, a2, fn(b1, b2) (==)(b1, b2, fn(c1, c2) eqA(c1, c2))))

effect interp<a, s>
  ctl delta(op: string, e0: evalue<a>, e1: evalue<a>): evalue<a>
  fun zero(v: evalue<a>): bool
  fun ask-env(): env<a> 
  ctl ret(v: evalue<a>): evalue<a>
  fun ext(a: a, v: evalue<a>): ()
  fun alloc(x: string): a
  ctl get(m: maybe<a>): evalue<a>
  fun traceR(r: evalue<a>): evalue<a>
  val show-addr: ((a) -> string)
  val eq-addr: (some<e> (a,a) -> e bool)
  fun show-store(): ()
  fun get-store(): linearMap<a, s>

effect fail<a>
  ctl fail(): evalue<a>

alias rinterp<a,s> = <exn,div,fail<a>,interp<a,s>>
fun local-env(env: env<a>, f: () -> <rinterp<a,s>|e> evalue<a>): <rinterp<a,s>|e> evalue<a>
  with override
    ctl delta(op, e0, e1) resume(delta(op, e0, e1))
    fun zero(v) zero(v)
    fun ask-env() env
    ctl ret(v) resume(ret(v))
    fun ext(a, v) ext(a, v)
    fun alloc(x) alloc(x)
    ctl get(m) resume(get(m))
    fun traceR(r) traceR(r)
    val show-addr = show-addr
    val eq-addr = eq-addr
    fun show-store() show-store()
    fun get-store() get-store()
  f()

fun ev(ev: (expr) -> <rinterp<a,s>|e> evalue<a>, e: expr): <rinterp<a,s>|e> evalue<a>
  // trace("Evaluating " ++ e.show)
  match e
      App(e0, e1) ->
        val v = ev(e0)
        match v
          Clos(Lam(x, e2), p') ->
            val v1 = ev(e1)
            val a = alloc(x)
            ext(a, v1)
            local-env(Cons((x, a), p'), fn() ev(e2))
          _ -> throw("Non closure in closure position")
      Num(n) -> NumV(n)
      Id(x) ->
        val p = ask-env()
        get(p.find(fn(a) a.fst == x).map(fn(a) a.snd))
      If0(e0, e1, e2) ->
        val cond = ev(e0)
        ev(if zero(cond) then e1 else e2)
      Op2(name, e0, e1) ->
        val v0 = ev(e0)
        val v1 = ev(e1)
        delta(name, v0, v1)
      Rec(fname, e0) ->
        val p = ask-env()
        val a = alloc(fname)
        val v = local-env(Cons((fname, a), p), fn() ev(e0))
        ext(a, v)
        ret(v)
      Lam(_, _) ->
        val p = ask-env()
        ret(Clos(e, p))

fun evnormal(e)
  with override
    final ctl fail()
      ErrorV
  ev(evnormal, e)

effect tell<a>
  fun tell(e: a): ()

fun evtell(e: expr)
  with override
    final ctl fail()
      ErrorV
  tell((e, ask-env(), get-store()))
  ev(evtell, e)

effect evdead
  fun get-dead(): linearSet<expr>
  fun mark-alive(e: expr): ()

fun evdead(e: expr)
  with override
    final ctl fail()
      ErrorV
  mark-alive(e)
  ev(evdead, e)

fun show(e: evalue<a>): string
  match e
    NumV(n) -> n.show
    Clos(_, _) -> "<closure>"
    ErrorV -> "<error>"

fun show(e: expr): string
  match e
    Num(n) -> n.show
    If0(e0, e1, e2) -> "if0 " ++ show(e0) ++ " then " ++ show(e1) ++ " else " ++ show(e2)
    Op2(op, e0, e1) -> "(" ++ show(e0) ++ " " ++ op ++ " " ++ show(e1) ++ ")"
    Id(x) -> x
    Rec(fname, e0) -> "rec " ++ fname ++ " = " ++ show(e0)
    Lam(v, e0) -> "fun " ++ v ++ " -> " ++ show(e0)
    App(e0, e1) -> "(" ++ show(e0) ++ " " ++ show(e1) ++ ")"  

fun show(s: list<(string, a)>, showA: (a) -> string): string
  s.show-list(fn(t) t.show-tuple(show, showA))

fun show(s: list<(a, evalue<a>)>, showA: (a) -> string): string
  s.show-list(fn(t) t.show-tuple(showA, show))

fun test-concrete(f: ((expr) -> <rinterp<int,evalue<int>>|e> evalue<int>), e: expr): <exn,div|e> evalue<int>
  with handler 
    final ctl fail() ErrorV
  var env := []
  val eq-addr =  fn(a: int, b: int) a == b
  var store := linearMap([], eq-addr)
  val showA = fn(i: int) show(i)
  with handler
    ctl delta(op, e0, e1)
      match (op, e0, e1)
        ("*", NumV(v0), NumV(v1)) -> resume(NumV(v0 * v1))
        ("+", NumV(v0), NumV(v1)) -> resume(NumV(v0 + v1))
        ("-", NumV(v0), NumV(v1)) -> resume(NumV(v0 - v1))
        ("/", NumV(v0), NumV(v1)) -> if v1 == 0 then fail() else resume(NumV(v0 / v1))
        _ -> throw("Unknown primitive operation " ++ op)
    fun zero(v)
      match v
        NumV(0) -> True
        _ -> False
    fun ask-env()
      env
    ctl ret(v)
      resume(v)
    fun ext(a, v)
      store := store.update(a, v, fn(_, n) n)
    fun alloc(x)
      val a = store.list.length
      a
    ctl get(m)
      match m
        Just(a) -> match store.maybeGet(a)
          Just(x) -> resume(x)
          Nothing -> throw("Variable not in the store")
        Nothing -> throw("Unbound variable")
    fun traceR(r)
      r.show.trace
      r
    val show-addr = showA
    fun show-store()
      store.list.show(showA).trace
    fun get-store()
      store
    val eq-addr = eq-addr
  mask<local>
    f(e)

fun injectConcrete(c: evalue<a>): interp<a,s> abvalue<a>
  match c
    NumV(i) -> Abvalue(Just(Elem(i)), Nothing)
    Clos(e, p) -> Abvalue(Nothing, Just(linearSet([Abclos(e, p)], fn(a, b) (==)(a, b, eq-addr))))
    ErrorV -> Abvalue(Nothing, Nothing)

// fun test-abstract(f: ((expr) -> <rinterp<int,abvalue>|e> evalue<e>), e: expr): <exn,div|e> linearSet<abvalue>
  // val eqV = fn(e1: abvalue, e2: abvalue) (==)(e1, e2, fn(a1, a2) a1 == a2)
//   with handler 
//     final ctl fail() linearSet([ErrorV], eqV)
//   var env := []
//   var store := linearMap([], fn(a: int, b: int) a == b)
//   val showA = fn(i: int) show(i)
//   with handler
//     return(x) linearSet([x], eqV)
//     ctl delta(op, e0, e1)
//       match (op, e0, e1)
//         ("*", NumV(v0), NumV(v1)) -> linearSet([resume(NumV(v0 * v1))], eqV)
//         ("+", NumV(v0), NumV(v1)) -> linearSet([resume(NumV(v0 + v1))], eqV)
//         ("-", NumV(v0), NumV(v1)) -> linearSet([resume(NumV(v0 - v1))], eqV)
//         ("/", NumV(v0), NumV(v1)) -> if v1 == 0 then fail() else linearSet([resume(NumV(v0 / v1))], eqV)
//         _ -> throw("Unknown primitive operation " ++ op)
//     fun zero(v)
//       match v
//         NumV(0) -> True
//         _ -> False
//     fun ask-env()
//       env
//     ctl ret(v)
//       resume(v)
//     fun ext(a, v)
//       store := store.update(a, v, fn(_, n) n)
//     fun alloc(x)
//       val a = store.list.length
//       a
//     ctl get(m)
//       match m
//         Just(a) -> match store.maybeGet(a)
//           Just(x) -> resume(x)
//           Nothing -> throw("Variable not in the store")
//         Nothing -> throw("Unbound variable")
//     fun traceR(r)
//       r.show.trace
//       r
//     val show-addr = showA
//     fun show-store()
//       store.list.show(showA).trace
//     fun get-store()
//       store
//   mask<local>
//     f(e)

fun test-evtell(e)
  with handler
    fun tell(x)
      val (a:expr, b:env<int>, c:linearMap<int,evalue<int>>) = x
      (a.show ++ "," ++ b.show(show) ++ "," ++ c.list.show(show)).println
  test-concrete(evtell, e)

fun test-evdead(e)
  var dead := linearSet(e.subexprs, fn(a: expr, b: expr) a == b)
  with handler
    fun get-dead()
      dead
    fun mark-alive(e1)
      dead := dead - e1
  val r = test-concrete(evdead, e)
  println("The following are dead expressions")
  dead.list.show-list(show).println
  println("Result of the program " ++ r.show)

fun main()
  test-concrete(evnormal, App(Rec("fact", Lam("n", If0(Id("n"), Num(1), Op2("*", Id("n"), App(Id("fact"), Op2("-", Id("n"), Num(1))))))), Num(10))).show.println
  test-evtell(Op2("*", Op2("+", Num(3), Num(4)), Num(9))).show.println
  // (if0 0 1 2)
  test-evdead(If0(Num(0), Num(1), Num(2)))
  // (lambda (x) x)
  test-evdead(Lam("x", Id("x")))
  // (if0 (/ 1 0) 2 3)
  test-evdead(If0(Op2("/", Num(1), Num(0)), Num(2), Num(3)))
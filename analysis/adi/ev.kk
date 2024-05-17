import std/data/linearmap
import std/data/linearset
import utils
import expr

alias env<a> = list<(string, a)>

type evalue<a>
  NumV(i: int)
  ClosV(c: clos<env<a>>)
  ErrorV

value struct clos<p>
  e: expr
  p: p

fun (==)(e1: env<int>, e2: env<int>): div bool
  (==)(e1, e2, fn(i1:int, i2: int) i1 == i2, show)

fun (==)(e1: evalue<a>, e2: evalue<a>, eqA: (a, a) -> <div|e> bool, showA: (a) -> <div|e> string): <div|e> bool
  with traceEq(e1, e2, fn(e:some<a> evalue<a>) e.show)
  match (e1, e2)
    (NumV(i1), NumV(i2)) -> i1 == i2
    (ClosV(c1), ClosV(c2)) -> (==)(c1, c2, fn(p1, p2) (==)(p1, p2, eqA, showA))
    (ErrorV, ErrorV) -> True
    _ -> False

fun (==)(e1: env<a>, e2: env<a>, eqA: (a, a) -> <div|e> bool, showA: (a) -> <div|e> string): <div|e> bool
  with traceEq(e1, e2, fn(e:some<a> env<a>) e.show-list(fn(t1) t1.show-tuple(show, showA)))
  match (e1, e2)
    (Nil, Nil) -> True
    (Cons((x1, a1), p1), Cons((x2, a2), p2)) -> x1 == x2 && eqA(a1, a2) && (==)(p1, p2, eqA, showA)
    _ -> False

fun (==)(c1: clos<p>, c2: clos<p>, eqEnv: (p, p) -> <div|e> bool): <div|e> bool
  c1.e == c2.e && eqEnv(c1.p, c2.p)

fun show(e: evalue<a>): string
  match e
    NumV(n) -> n.show
    ClosV(_) -> "<closure>"
    ErrorV -> "<error>"

fun show(c: clos<p>, showP: (p) -> <div|e> string): <div|e> string
  c.e.show ++ " " ++ showP(c.p)

fun show(s: list<(a, evalue<a>)>, showA: (a) -> e string): e string
  s.show-list(fn(t) t.show-tuple(showA, show))

effect endet<a, s, p>
  ctl delta(op: string, e0: s, e1: s): s
  ctl zero(v: s): bool
  ctl closures(v: s): clos<p>
  ctl get(m: maybe<a>): s

effect fail<s>
  ctl fail(): s

effect primop<a, s>
  fun inj(v: evalue<a>): s 
  val show-addr: ((a) -> string)
  val eq-addr: (some<e> (a,a) -> e bool)
  fun traceR(r: s): s

effect eenv<a, p>
  fun ask-env(): p 
  fun find-env(s: string): maybe<a>

effect estore<a, s>
  fun alloc(x: string): a
  fun ext(a: a, v: s): ()
  fun get-store(): linearMap<a, s>
  fun put-store(s: linearMap<a, s>): ()

alias rinterp<a,s> = <exn,div,primop<a,s>,eenv<a,env<a>>,estore<a,s>,endet<a,s,env<a>>,fail<s>>

fun local-env(env: env<a>, f: () -> <rinterp<a,s>|e> s): <rinterp<a,s>|e> s
  with override
    fun ask-env() env
    fun find-env(s) env.find(fn(t) t.fst == s).map(fn(t) t.snd)
  f()

fun default-env(f)
  val env = []
  with handler
    fun ask-env()
      env
    fun find-env(s)
      Nothing
  f()

fun ev(ev: (expr) -> <rinterp<a,s>|e> s, e: expr): <rinterp<a,s>|e> s
  // trace("Evaluating " ++ e.show)
  match e
      App(e0, e1) ->
        val v = ev(e0)
        match closures(v)
          Clos(Lam(x, e2), p') ->
            val v1 = ev(e1)
            val a = alloc(x)
            ext(a, v1)
            local-env(Cons((x, a), p'), fn() ev(e2))
          _ -> throw("Non closure in closure position")
      Num(n) -> inj(NumV(n))
      Id(x) ->
        get(find-env(x))
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
        v
      Lam(_, _) ->
        val p = ask-env()
        inj(ClosV(Clos(e, p)))
      Let(x, e0, e1) ->
        val v0 = ev(e0)
        val a = alloc(x)
        ext(a, v0)
        e1.map(fn(e') local-env(Cons((x, a), ask-env()), fn() ev(e'))).last.unjust

fun ev'(evx: (expr) -> <rinterp<a,s>|e> s): ((expr) -> <rinterp<a,s>|e> s)
  fn(e:expr) 
    ev(evx, e)

fun evnormal(ev0)
  fn (ev)
    fn(e)
      with handleNdet
      with handler final ctl fail()
        ErrorV
      mask behind<endet>
        mask behind<fail>
          ev0(ev)(e)

fun doevnormal(e)
  fix(evnormal(ev'))(e)

effect tell<a,s>
  fun tell(e: a, indent: int): ()
  fun tellResult(e: s, indent: int): s
  val expressionDepth: int

fun evtell(ev0)
  fn(ev)
    fn(e)
      with override
        fun tell(e', d)
          tell(e', d)
        fun tellResult(e', d)
          tellResult(e', d)
        val expressionDepth = expressionDepth + 1
      tell((e, ask-env(), get-store()), expressionDepth)
      tellResult(ev0(ev)(e), expressionDepth)

fun doevtell(e)
  fix(evtell(evnormal(ev')))(e)

effect evdead
  fun get-dead(): linearSet<expr>
  fun mark-alive(e: expr): ()

fun evdead(ev0)
  fn(ev)
    fn(e)
      mark-alive(e)
      ev0(ev)(e)

fun doevdead(e)
  fix(evdead(evnormal(ev')))(e)

val eqAddr = fn(a: int, b: int) a == b
val showA = fn(i: int) show(i)

fun defaultNdet(f)
  with handler
    fun delta(op, e0, e1)
      throw("Unhandled")
    fun closures(s)
      throw("Unhandled")
    fun zero(v)
      throw("Unhandled")
    fun get(a)
      throw("Unhandled")
  f()

fun handleNdet(f)
  with handler
    ctl delta(op, e0, e1)
      match (op, e0, e1)
        ("*", NumV(v0), NumV(v1)) -> resume(NumV(v0 * v1))
        ("+", NumV(v0), NumV(v1)) -> resume(NumV(v0 + v1))
        ("-", NumV(v0), NumV(v1)) -> resume(NumV(v0 - v1))
        ("/", NumV(v0), NumV(v1)) -> if v1 == 0 then fail() else resume(NumV(v0 / v1))
        _ -> throw("Unknown primitive operation " ++ op)
    ctl closures(c)
      match c
        ClosV(c') -> resume(c')
        _ -> fail()
    fun zero(v)
      match v
        NumV(0) -> True
        _ -> False
    fun get(m)
      match m
        Just(a) -> match get-store().maybeGet(a)
          Just(x) -> x
          Nothing -> throw("Variable " ++ show-addr(a) ++ " not in the store") 
        Nothing -> throw("Unbound variable")
  f()

fun test-concrete(f: ((expr) -> <rinterp<int,evalue<int>>|e> evalue<int>), e: expr): <div,exn|e> evalue<int>
  var env := []
  var store := linearMap([], eqAddr, fn(a:evalue<int>, b:evalue<int>) (==)(a, b, eqAddr, showA), showA, show)
  with handler
    fun inj(e1)
      e1
    fun traceR(r:evalue<int>)
      r.show.trace
      r
    val show-addr = showA
    val eq-addr = eqAddr
  with handler
    fun ask-env()
      env
    fun find-env(s)
      Nothing
  with handler
    fun alloc(x)
      val a = store.list.length
      a
    fun ext(a, v)
      store := store.update(a, v, fn(_, n) n)
    fun get-store()
      store
    fun put-store(s)
      store := s
  with handler
    final ctl fail() ErrorV
  with defaultNdet
  f(e)
import newstd/data/linearmap
import newstd/data/linearset
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
  (==)(e1, e2, fn(i1:int, i2: int) i1 == i2)

fun (==)(e1: evalue<a>, e2: evalue<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (e1, e2)
    (NumV(i1), NumV(i2)) -> i1 == i2
    (ClosV(c1), ClosV(c2)) -> (==)(c1, c2, fn(p1, p2) (==)(p1, p2, eqA))
    (ErrorV, ErrorV) -> True
    _ -> False

fun (==)(e1: env<a>, e2: env<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (e1, e2)
    (Nil, Nil) -> True
    (Cons((x1, a1), p1), Cons((x2, a2), p2)) -> x1 == x2 && eqA(a1, a2) && (==)(p1, p2, eqA)
    _ -> False

fun (==)(c1: clos<p>, c2: clos<p>, eqEnv: (p, p) -> <div|e> bool): <div|e> bool
  c1.e == c2.e && eqEnv(c1.p, c2.p)

fun show(e: evalue<a>): string
  match e
    NumV(n) -> n.show
    ClosV(_) -> "<closure>"
    ErrorV -> "<error>"

fun show(s: list<(a, evalue<a>)>, showA: (a) -> e string): e string
  s.show-list(fn(t) t.show-tuple(showA, show))

effect interp<a, s, p>
  ctl delta(op: string, e0: s, e1: s): s
  fun zero(v: s): bool
  fun ask-env(): p 
  fun inj(v: evalue<a>): s 
  ctl ret(v: s): s
  ctl closures(v: s): clos<p>
  fun ext(a: a, v: s): ()
  fun alloc(x: string): a
  ctl get(m: maybe<a>): s
  fun traceR(r: s): s
  val show-addr: ((a) -> string)
  val eq-addr: (some<e> (a,a) -> e bool)
  fun show-store(): ()
  fun get-store(): linearMap<a, s>
  fun put-store(s: linearMap<a, s>): ()
  fun find-env(s: string): maybe<a>

effect fail<s>
  ctl fail(): s

alias rinterp<a,s> = <exn,div,fail<s>,interp<a,s,env<a>>>
fun local-env(env: env<a>, f: () -> <rinterp<a,s>|e> s): <rinterp<a,s>|e> s
  with override
    ctl delta(op, e0, e1) resume(delta(op, e0, e1))
    fun zero(v) zero(v)
    fun ask-env() env
    fun inj(v) inj(v)
    ctl ret(v) resume(ret(v))
    ctl closures(v) resume(closures(v))
    fun ext(a, v) ext(a, v)
    fun alloc(x) alloc(x)
    ctl get(m) resume(get(m))
    fun traceR(r) traceR(r)
    val show-addr = show-addr
    val eq-addr = eq-addr
    fun show-store() show-store()
    fun get-store() get-store()
    fun put-store(s) put-store(s)
    fun find-env(s) env.find(fn(t) t.fst == s).map(fn(t) t.snd)
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
        ret(v)
      Lam(_, _) ->
        val p = ask-env()
        inj(ClosV(Clos(e, p)))
      Let(x, e0, e1) ->
        val v0 = ev(e0)
        val a = alloc(x)
        ext(a, v0)
        e1.map(fn(e') local-env(Cons((x, a), ask-env()), fn() ev(e'))).last.unjust

fun ev'(evx: (expr) -> <rinterp<a,s>|e> s): ((expr) -> <rinterp<a,s>|e> s)
  fn(e:expr) ev(evx, e)

fun evnormal(e)
  fix(ev')(e)

effect tell<a>
  fun tell(e: a): ()

fun evtell(ev0)
  fn(ev)
    fn(e)
      tell((e, ask-env(), get-store()))
      ev0(ev)(e)

fun doevtell(e)
  fix(evtell(ev'))(e)

effect evdead
  fun get-dead(): linearSet<expr>
  fun mark-alive(e: expr): ()

fun evdead(ev0)
  fn(ev)
    fn(e)
      mark-alive(e)
      ev0(ev)(e)

fun doevdead(e)
  fix(evdead(ev'))(e)

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
    fun traceR(r:evalue<int>)
      r.show.trace
      r
    val show-addr = showA
    fun show-store()
      store.list.show(showA).trace
    fun get-store()
      store
    ctl closures(c)
      match c
        ClosV(c') -> resume(c')
        _ -> fail()
    fun inj(e1)
      e1
    fun find-env(s)
      Nothing
    fun put-store(s)
      store := s
    val eq-addr = eq-addr
  mask<local>
    f(e)
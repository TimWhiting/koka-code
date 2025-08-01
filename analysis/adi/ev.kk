import std/data/linearmap
import std/data/linearset
import utils
import expr

alias env<a> = linearMap<string, a>

type evalue<a>
  NumV(i: int)
  ClosV(c: clos<env<a>>)
  ErrorV

value struct clos<p>
  e: expr
  p: p

fun clos/(==)(c1: clos<p>, c2: clos<p>, ?(==): (p, p) -> <div|e> bool): <div|e> bool
  c1.e == c2.e && c1.p == c2.p

fun evalue/(==)(e1: evalue<a>, e2: evalue<a>, ?(==): (a, a) -> <div|e> bool): <div|e> bool
  match (e1, e2)
    (NumV(i1), NumV(i2)) -> i1 == i2
    (ClosV(c1), ClosV(c2)) -> clos/(==)(c1, c2)
    (ErrorV, ErrorV) -> True
    _ -> False

fun clos/show(c: clos<p>): <div|e> string
  "Clos(" ++ c.e.show ++ ")"

fun evalue/show(e: evalue<a>): string
  match e
    NumV(n) -> n.show
    ClosV(_) -> "<closure>"
    ErrorV -> "<error>"

effect endet<a, s, p>
  ctl delta(op: string, e0: s, e1: s): s
  ctl zero(v: s): bool
  ctl closures(v: s): clos<p>
  ctl dereference(m: maybe<a>): s

effect fail<s>
  ctl fail(): s

effect primop<a, s>
  fun show-addr(a: a): string
  fun eq-addr(a1: a, a2: a): bool
  fun inj(v: evalue<a>): s 
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
    fun find-env(s) env.lookup(s)
  f()

fun default-env(f)
  val env = LinearMap([])
  with handler
    fun ask-env() env
    fun find-env(s) Nothing
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
            local-env(p'.set(x, a))
              ev(e2)
          _ -> throw("Non closure in closure position")
      Num(n) -> inj(NumV(n))
      Id(x) -> dereference(find-env(x))
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
        val v = local-env(p.set(fname, a))
          ev(e0)
        ext(a, v)
        v
      Lam(_, _) ->
        val p = ask-env()
        inj(ClosV(Clos(e, p)))
      Let(x, e0, e1) ->
        val v0 = ev(e0)
        val a = alloc(x)
        ext(a, v0)
        e1.map(fn(e') local-env(ask-env().set(x, a), {ev(e')})).last.unjust

fun ev'(evx: (expr) -> <rinterp<a,s>|e> s): ((expr) -> <rinterp<a,s>|e> s)
  fn(e:expr) 
    ev(evx, e)

fun evnormal(ev0)
  fn(ev)
    fn(e)
      with handleNdet
      with handler final ctl fail() ErrorV
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

// fun doevtell(e)
//   fix(evtell(evnormal(ev')))(e)

effect evdead
  fun get-dead(): linearSet<expr>
  fun mark-alive(e: expr): ()

fun evdead(ev0)
  fn(ev)
    fn(e)
      mark-alive(e)
      ev0(ev)(e)

// fun doevdead(e)
//   fix(evdead(evnormal(ev')))(e)

fun defaultNdet(f)
  with handler
    fun delta(op, e0, e1) throw("Unhandled")
    fun closures(s) throw("Unhandled")
    fun zero(v) throw("Unhandled")
    fun dereference(a) throw("Unhandled")
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
    fun dereference(m)
      match m
        Just(a) -> 
          match get-store().lookup(a, eq-addr)
            Just(x) -> x
            Nothing -> throw("Variable " ++ a.show-addr ++ " not in the store") 
        Nothing -> throw("Unbound variable")
  f()

fun test-concrete(f: ((expr) -> <rinterp<int,evalue<int>>|e> evalue<int>), e: expr): <div,exn|e> evalue<int>
  var env := LinearMap([])
  var store: linearMap<int,evalue<int>> := LinearMap([])
  with handler
    fun show-addr(a) a.int/show
    fun eq-addr(a1: int, a2) a1 == a2
    fun inj(e1) e1
    fun traceR(r:evalue<int>)
      r.show.trace
      r
  with handler
    fun ask-env() env
    fun find-env(s) Nothing
  with handler
    fun alloc(x) store.list.length
    fun ext(a, v) store := store.update(a, v, fn(_, n) n)
    fun get-store() store
    fun put-store(s) store := s
  with final ctl fail() ErrorV
  with defaultNdet
  f(e)
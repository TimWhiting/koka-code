import analysis/cps/sexpr
import newstd/data/linearmap
import newstd/data/linearset

type expr
  Num(i: int)
  If0(e0: expr, e1: expr, e2: expr)
  Op2(op: string, e0: expr, e1: expr)
  Id(x: string)
  Rec(x: string, e: expr)
  Lam(v: string, e: expr)
  App(e0: expr, e1: expr)
  Let(v: string, e0: expr, e1s: list<expr>)

fun (==)(l1: list<a>, l2: list<a>, eq: (a, a) -> e bool): e bool
  match (l1, l2)
    (Nil, Nil) -> True
    (Cons(x1, p1), Cons(x2, p2)) -> eq(x1, x2) && (==)(p1, p2, eq)
    _ -> False

fun (==)(e1: expr, e2: expr): div bool
  match (e1, e2)
    (Num(i1), Num(i2)) -> i1 == i2
    (If0(e1, e2, e3), If0(e4, e5, e6)) -> e1 == e4 && e2 == e5 && e3 == e6
    (Op2(op1, e1, e2), Op2(op2, e3, e4)) -> op1 == op2 && e1 == e3 && e2 == e4
    (Id(x1), Id(x2)) -> x1 == x2
    (Rec(x1, e1), Rec(x2, e2)) -> x1 == x2 && e1 == e2
    (Lam(x1, e1), Lam(x2, e2)) -> x1 == x2 && e1 == e2
    (App(e1, e2), App(e3, e4)) -> e1 == e3 && e2 == e4
    (Let(x1, e1, e2), Let(x2, e3, e4)) -> x1 == x2 && e1 == e3 && (==)(e2, e4, (==))
    _ -> False

fun subexprs(e: expr): div list<expr>
  match e
    Num(_) -> [e]
    If0(e0, e1, e2) -> Cons(e, e0.subexprs ++ e1.subexprs ++ e2.subexprs)
    Op2(_, e0, e1) -> Cons(e, e0.subexprs ++ e1.subexprs)
    Id(_) -> [e]
    Rec(_, e0) -> Cons(e, e0.subexprs)
    Lam(_, e0) -> Cons(e, e0.subexprs)
    App(e0, e1) -> Cons(e, e0.subexprs ++ e1.subexprs)
    Let(_, e0, e1) -> Cons(e, e0.subexprs ++ e1.map(subexprs).concat)

alias env<a> = list<(string, a)>

type evalue<a>
  NumV(i: int)
  ClosV(c: clos<env<a>>)
  ErrorV

value type lattice<a>
  Top
  Bottom
  Elem(a: a)

value struct clos<p>
  e: expr
  p: p

alias abenv<a> = list<(string, a)>;

struct abvalue<a>
  num: maybe<lattice<int>>
  clos: maybe<linearSet<clos<env<a>>>>;

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

fun (==)(l1: lattice<a>, l2: lattice<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (l1, l2)
    (Top, Top) -> True
    (Bottom, Bottom) -> True
    (Elem(a1), Elem(a2)) -> eqA(a1, a2)
    _ -> False

fun (==)(c1: clos<p>, c2: clos<p>, eqEnv: (p, p) -> <div|e> bool): <div|e> bool
  c1.e == c2.e && eqEnv(c1.p, c2.p)

fun (==)(m1: maybe<a>, m2: maybe<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (m1, m2)
    (Just(a1), Just(a2)) -> eqA(a1, a2)
    (Nothing, Nothing) -> True
    _ -> False

fun (==)(v1: abvalue<a>, v2: abvalue<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  val numEq = (==)(v1.num, v2.num, fn(a1, a2) (==)(a1, a2, (==)))
  if !numEq then return False
  (==)(v1.clos, v2.clos, fn(m1, m2) m1 == m2)

alias cache-key<a,s,p> = (expr, p, linearMap<a, s>)
alias cache-entry<a,s> = linearSet<(s, linearMap<a, s>)>
alias cache<a,s,p> = linearMap<(expr, p, linearMap<a, s>), cache-entry<a, s>>

effect ecache<a, s, p>
  fun get-cache-out(): cache<a,s,p>
  fun set-cache-out(c: cache<a,s,p>): ()
  fun get-cache-in(): cache<a,s,p>
  fun set-cache-in(c: cache<a,s,p>): ()
  fun put-cache-out(c: (expr, p, linearMap<a,s>), s: cache-entry<a,s>): ()
  ctl visit-cache(s: cache-entry<a,s>): (s, linearMap<a,s>)
  fun update-cache(c: (expr, p, linearMap<a, s>), v: s, s: linearMap<a,s>): ()
  val eq-v-store: (some<e> ((s, linearMap<a,s>), (s, linearMap<a,s>)) -> e bool)

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

fun fix(f)
  fn(x)
    f(fix(f))(x)

fun ev'(evx: (expr) -> <rinterp<a,s>|e> s): ((expr) -> <rinterp<a,s>|e> s)
  fn(e:expr) ev(evx, e)

fun evcache(ev0)
  fn(ev)
    fn(e)
      val p = ask-env()
      val s = get-store()
      val config = (e, p, s)
      val out = get-cache-out()
      if out.containsKey(config) then
        val v-store = out.get(config)
        val (v, store) = visit-cache(v-store)
        put-store(store)
        ret(v)
      else
        val inC = get-cache-in()
        val v-store = inC.getDefault(config, linearSet([], eq-v-store))
        put-cache-out(config, v-store)
        val v = ev0(ev)(e)
        val s' = get-store()
        update-cache(config, v, s')
        ret(v)

// fun fixcache(eval)
//   with handler
//     fun get-cache-out() get-cache-out()
//     fun set-cache-out(c) set-cache-out(c)
//     fun get-cache-in() get-cache-in()
//     fun set-cache-in(s) set-cache-in(s)
//     ctl visit-cache(c) resume(visit-cache(c))
//     fun put-cache-out(c,s) put-cache-out(c,s)
//     fun update-cache(c, v, s) update-cache(c, v, s)
//     val eq-v-store = eq-v-store
//   fn(e)
//     val p = ask-env()
//     val s = get-store()
//     val config = (e, p, s)
//     val newCache = mlfp() fn(cache)
//       set-cache-out(linearMap([], eqConfig))
//       put-store(s)
//       set-cache-in(cache)
//       val res = eval(e)
//       get-cache-out()
//     val vstore = newCache.get(config)
//     val (v, store) = visit-cache(vstore)
//     put-store(store)
//     ret(v)

alias abcache = cache<int, abvalue<int>, env<int>>
// fun mlfp(f: (abcache) -> <rinterp<int, abcache>|e> abcache)
//   fun loop(x:abcache = linearMap([], eqConfig)): <rinterp<int, abcache>|e> abcache
//     val x' = f(x)
//     if eqCache(x', x) then x
//     else loop(x')
//   loop

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

fun show(e: evalue<a>): string
  match e
    NumV(n) -> n.show
    ClosV(_) -> "<closure>"
    ErrorV -> "<error>"

fun show(e: expr): div string
  match e
    Num(n) -> n.show
    If0(e0, e1, e2) -> "if0 " ++ show(e0) ++ " then " ++ show(e1) ++ " else " ++ show(e2)
    Op2(op, e0, e1) -> "(" ++ show(e0) ++ " " ++ op ++ " " ++ show(e1) ++ ")"
    Id(x) -> x
    Rec(fname, e0) -> "rec " ++ fname ++ " = " ++ show(e0)
    Lam(v, e0) -> "fun " ++ v ++ " -> " ++ show(e0)
    App(e0, e1) -> "(" ++ show(e0) ++ " " ++ show(e1) ++ ")"  
    Let(v, e0, e1) -> "let " ++ v ++ " = " ++ show(e0) ++ " in " ++ show-list(e1, show)

fun show(l: lattice<a>, showA: (a) -> e string): e string
  match l
    Top -> "⊤"
    Bottom -> "⊥"
    Elem(a) -> showA(a)

fun show(m: maybe<a>, showA: (a) -> e string): e string
  match m
    Just(a) -> showA(a)
    Nothing -> "⊥"

fun show(a: abvalue<a>, showA: (a) -> e string): <div|e> string
  a.num.show(fn(s) s.show(show)) ++ " {" ++ a.clos.show(fn(s) s.list.show-list(fn(c) c.e.show)) ++ "}"

fun show(s: list<(string, a)>, showA: (a) -> e string): e string
  s.show-list(fn(t) t.show-tuple(show, showA))

fun show(s: list<(a, evalue<a>)>, showA: (a) -> e string): e string
  s.show-list(fn(t) t.show-tuple(showA, show))

fun show(s: list<(a, abvalue<a>)>, showA: (a) -> <> string): div string
  s.show-list(fn(t) t.show-tuple(showA, fn(s') s'.show(showA)))

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

fun injectConcrete(c: evalue<a>, eqA: some<e> (a, a) -> e bool): abvalue<a>
  match c
    NumV(i) -> Abvalue(Just(Elem(i)), Nothing)
    ClosV(c) -> Abvalue(Nothing, Just(linearSet([c], fn(a, b) (==)(a, b, fn(p1, p2) (==)(p1, p2, eqA)))))
    ErrorV -> Abvalue(Nothing, Nothing)

fun join(m1: maybe<a>, m2: maybe<a>, joinA: (a, a) -> e a): e maybe<a>
  match (m1, m2)
    (Just(a1), Just(a2)) -> Just(joinA(a1, a2))
    (_, Just(a2)) -> Just(a2)
    (Just(a1), _) -> Just(a1)
    (Nothing, Nothing) -> Nothing

fun join(n: lattice<int>, n': lattice<int>): lattice<int>
  match (n, n')
    (Top, _) -> Top
    (_, Top) -> Top
    (Bottom, _) -> n'
    (_, Bottom) -> n
    (Elem(i), Elem(i')) | i == i' -> Elem(i)
    _ -> Top

fun join(e: abvalue<a>, e': abvalue<a>): e abvalue<a>
  val num = e.num.join(e'.num, fn(a, b) join(a, b))
  val clos = e.clos.join(e'.clos, fn(a, b) a + b)
  Abvalue(num, clos)

val topN = Abvalue(Just(Top), Nothing)

alias config = cache-key<int, abvalue<int>, env<int>>

fun (==)(e1: env<int>, e2: env<int>): div bool
  (==)(e1, e2, fn(i1:int, i2: int) i1 == i2)

fun eqStore(s1: linearMap<int, abvalue<int>>, s2: linearMap<int, abvalue<int>>)
  (==)(s1, s2, fn(av1, av2) (==)(av1, av2, (==)))

fun eqConfig(c1: config, c2: config): div bool
  c1.fst == c2.fst && c1.snd == c2.snd && eqStore(c1.thd, c2.thd)

alias cacheval = (abvalue<int>, linearMap<int,abvalue<int>>)
fun eqCacheValue(s1: cacheval, s2: cacheval): div bool
  (==)(s1.fst, s2.fst, (==)) && eqStore(s1.snd, s2.snd)

fun eqCache(c1: cache<int, abvalue<int>, env<int>>, c2: cache<int, abvalue<int>, env<int>>)
  (==)(c1, c2, fn(s1, s2) (==)(s1, s2))

val emptyCacheValStore = linearSet([(Abvalue(Nothing, Nothing), linearMap([], fn(i1, i2: int) i1 == i2))], eqCacheValue)

fun test-abstract(f: ((expr) -> <rinterp<int,abvalue<int>>|e> abvalue<int>), e: expr): <exn,div|e> abvalue<int>
  val eqAddr = fn(a: int, b: int) a == b
  val eqV = fn(e1: abvalue<int>, e2: abvalue<int>) (==)(e1, e2, fn(a1, a2) a1 == a2)
  with handler 
    final ctl fail() injectConcrete(ErrorV, eqAddr)
  var env := []
  var store:linearMap<int, abvalue<int>> := linearMap([], eqAddr)
  val showA = fn(i: int) show(i)
  var xmap := linearMap([], fn(s1:string, s2:string) s1 == s2)
  var cachein := linearMap([], eqConfig)
  var cacheout := linearMap([], eqConfig)
  with handler
    ctl delta(op, e0, e1)
      match (op, e0, e1)
        ("*", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> resume(injectConcrete(NumV(v0 * v1), eqAddr))
        ("+", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> resume(injectConcrete(NumV(v0 + v1), eqAddr))
        ("-", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> resume(injectConcrete(NumV(v0 - v1), eqAddr))
        ("/", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> if v1 == 0 then fail() else resume(injectConcrete(NumV(v0 / v1), eqAddr))
        ("*", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> resume(topN)
        ("+", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> resume(topN)
        ("-", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> resume(topN)
        ("/", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> fail().join(resume(topN))
        _ -> throw("Unknown primitive operation " ++ op)
    fun zero(v)
      match v
        Abvalue(Just(Elem(0)), _) -> True
        _ -> False
    fun ask-env()
      env
    ctl closures(c)
      match c
        Abvalue(_, Just(c')) -> c'.list.foldl(injectConcrete(ErrorV, eqAddr)) fn(acc:abvalue<int>, c2: clos<env<int>>) 
          acc.join(resume(c2))
        _ -> injectConcrete(ErrorV, eqAddr)
    ctl ret(v)
      resume(v)
    fun ext(a, v)
      store := store.update(a, v, fn(o, n) o.join(n))
    fun alloc(x)
      match xmap.maybeGet(x)
        Just(a) -> a
        Nothing ->
          val a = store.list.length
          xmap := xmap.update(x, a, fn(_, n) n)
          a
    ctl get(m)
      match m
        Just(a) -> match store.maybeGet(a)
          Just(x) -> resume(x)
          Nothing -> throw("Variable not in the store")
        Nothing -> throw("Unbound variable")
    fun traceR(r: abvalue<int>)
      r.show(showA).trace
      r
    val show-addr = showA
    val eq-addr = eqAddr
    fun show-store()
      store.show(showA, fn(v) show(v, show)).trace
    fun get-store()
      store
    fun find-env(s)
      Nothing
    fun inj(e1)
      injectConcrete(e1, eqAddr)
    fun put-store(s)
      store := s
    // val eq-v-store = fn(a, b) False
    // fun get-cache-in() cachein
    // fun get-cache-out() cacheout
    // fun put-cache-out(c, s)
    //   cacheout := cacheout.update(c, s, fn(_, n) n)
    // ctl visit-cache(c) c.list.foldl(injectConcrete(ErrorV, eqAddr)) fn(acc: abvalue<int>, c2: cacheval)
    //   val (v, s) = c2
    //   acc.join(resume((v, s)))
    // fun update-cache(c, v, s)
    //   cacheout := cacheout.update(c, emptyCacheValStore.add((v, s)), fn(o, n) o.add((v, s)))
  mask<local>
    f(e)


fun test-evtell-abs(e)
  with handler
    fun tell(x)
      val (a:expr, b:env<int>, c:linearMap<int,abvalue<int>>) = x
      (a.show ++ "," ++ b.show(show) ++ "," ++ c.list.show(show)).println
  test-abstract(doevtell, e)

fun test-evtell(e)
  with handler
    fun tell(x)
      val (a:expr, b:env<int>, c:linearMap<int,evalue<int>>) = x
      (a.show ++ "," ++ b.show(show) ++ "," ++ c.list.show(show)).println
  test-concrete(doevtell, e)

fun test-evdead(e)
  var dead := linearSet(e.subexprs, fn(a: expr, b: expr) a == b)
  with handler
    fun get-dead()
      dead
    fun mark-alive(e1)
      dead := dead - e1
  val r = test-concrete(doevdead, e)
  println("The following are dead expressions")
  dead.list.show-list(show).println
  println("Result of the program " ++ r.show)

fun test-abstract-normal(e)
  test-abstract(doevtell, e).show(show).println

fun test-concrete-variations()
  test-concrete(evnormal, App(Rec("fact", Lam("n", If0(Id("n"), Num(1), Op2("*", Id("n"), App(Id("fact"), Op2("-", Id("n"), Num(1))))))), Num(10))).show.println
  test-evtell(Op2("*", Op2("+", Num(3), Num(4)), Num(9))).show.println
  // (if0 0 1 2)
  test-evdead(If0(Num(0), Num(1), Num(2)))
  // (lambda (x) x)
  test-evdead(Lam("x", Id("x")))
  // (if0 (/ 1 0) 2 3)
  test-evdead(If0(Op2("/", Num(1), Num(0)), Num(2), Num(3)))

fun main()
  // (let ((f (lambda (x) x))) (f 1) (f 2))
  test-evtell-abs(Let("f", Lam("x", Id("x")), [App(Id("f"), Num(1) ), App(Id("f"), Num(2))])).show(show).println
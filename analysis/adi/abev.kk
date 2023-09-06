import expr
import utils
import newstd/data/linearset
import newstd/data/linearmap
import ev

value type lattice<a>
  Top
  Bottom
  Elem(a: a)

struct abvalue<a>
  num: maybe<lattice<int>>
  clos: maybe<linearSet<clos<env<a>>>>;

alias config = cache-key<int, abvalue<int>, env<int>>
alias cache-key<a,s,p> = (expr, p, linearMap<a, s>)

val topN = Abvalue(Just(Top), Nothing)

fun show(l: lattice<a>, showA: (a) -> e string): e string
  match l
    Top -> "⊤"
    Bottom -> "⊥"
    Elem(a) -> showA(a)

fun show(a: abvalue<a>, showA: (a) -> <div|e> string): <div|e> string
  a.num.show(fn(s) s.show(show)) ++ " {" ++ a.clos.show(fn(s) s.list.show-list(fn(c) c.e.show)) ++ "}"

fun show(s: list<(a, abvalue<a>)>, showA: (a) -> <div|e> string): <div|e> string
  s.show-list(fn(t) t.show-tuple(showA, fn(s') s'.show(showA)))

fun (==)(l1: lattice<a>, l2: lattice<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (l1, l2)
    (Top, Top) -> True
    (Bottom, Bottom) -> True
    (Elem(a1), Elem(a2)) -> eqA(a1, a2)
    _ -> False

fun (==)(v1: abvalue<a>, v2: abvalue<a>, eqA: (a, a) -> <div|e> bool, showA: (a) -> <div|e> string): <div|e> bool
  with traceEq(v1, v2, fn(v: some<a> abvalue<a>) v.show(showA))
  (==)(v1.num, v2.num, fn(a1, a2) (==)(a1, a2, (==)), fn(l) l.show(show)) && (==)(v1.clos, v2.clos, fn(m1, m2) m1 == m2, fn(m) m.show)

fun eqConfig(c1: config, c2: config): div bool
  c1.fst == c2.fst && c1.snd == c2.snd && c1.thd == c2.thd

fun injectConcrete(c: evalue<a>, eqA: some<e> (a, a) -> <div|e> bool, showA: some<e> (a) -> <div|e> string): abvalue<a>
  match c
    NumV(i) -> Abvalue(Just(Elem(i)), Nothing)
    ClosV(c) -> Abvalue(Nothing, Just(linearSet([c], fn(a, b) (==)(a, b, fn(p1, p2) (==)(p1, p2, eqA, showA)), fn(s) s.show(fn(e) e.show(showA)))))
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

fun join(e: linearMap<int, abvalue<int>>, e': linearMap<int, abvalue<int>>): e linearMap<int,abvalue<int>>
  e'.list.foldl(e) fn(acc, (k1, v1))
    acc.set(k1, v1)

val eqAbsV = fn(e1: abvalue<int>, e2: abvalue<int>) (==)(e1, e2, fn(a1, a2) a1 == a2, showA)
val bottom = Abvalue(Nothing, Nothing)

fun injC(c: evalue<int>): abvalue<int>
  injectConcrete(c, eqAddr, showA)

fun handleAbsNdet(f)
  handle(f)
    ctl delta(op, e0, e1)
      match (op, e0, e1)
        ("*", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> resume(injC(NumV(v0 * v1)))
        ("+", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> resume(injC(NumV(v0 + v1)))
        ("-", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> resume(injC(NumV(v0 - v1)))
        ("/", Abvalue(Just(Elem(v0)), _), Abvalue(Just(Elem(v1)), _)) -> if v1 == 0 then injC(ErrorV) else resume(injC(NumV(v0 / v1)))
        ("*", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> resume(topN)
        ("+", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> resume(topN)
        ("-", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> resume(topN)
        ("/", Abvalue(Just(v0), _), Abvalue(Just(v1), _)) | v0.is-top || v1.is-top -> resume(topN)
        ("-", _, _) -> injC(ErrorV)
        ("*", _, _) -> injC(ErrorV)
        ("+", _, _) -> injC(ErrorV)
        ("/", _, _) -> injC(ErrorV)
        _ -> 
          throw("Unknown primitive operation " ++ op ++ " " ++ e0.show(showA) ++ " " ++ e1.show(showA))
    ctl zero(v)
      match v
        Abvalue(Just(Elem(0)), _) -> resume(True)
        Abvalue(Just(_), _) -> resume(True).join(resume(False))
        _ -> resume(False)
    ctl closures(c)
      match c
        Abvalue(_, Just(c')) -> c'.list.foldl(injC(ErrorV)) fn(acc:abvalue<int>, c2: clos<env<int>>) 
          acc.join(resume(c2))
        _ -> injC(ErrorV)
    ctl get(m)
      match m
        Just(a) -> match get-store().maybeGet(a)
          Just(x) -> resume(x)
          Nothing -> throw("Variable " ++ showA(a) ++ " not in the store " ++ get-store().show)
        Nothing -> throw("Unbound variable")

fun handleAbsValue(f)
  handle(f)
    fun inj(e1)
      injC(e1)
    fun traceR(r: abvalue<int>)
      ("Result: " ++ r.show(showA)).trace
      r
    val show-addr = showA
    val eq-addr = eqAddr

val emptyAbsStore = linearMap([], eqAddr, fn(a:abvalue<int>, b:abvalue<int>) (==)(a, b, eqAddr, showA), showA, fn(v) v.show(showA))

fun handle-store(f)
  var store := emptyAbsStore
  var xmap: linearMap<string, int> := linearMap([], fn(s1:string, s2:string) s1 == s2, fn(i1:int, i2:int) i1 == i2, show, show)
  with handler
    fun ext(a, v)
      store := store.update(a, v, fn(o, n) o.join(n))
    fun alloc(x)
      match xmap.maybeGet(x)
        Just(a) -> a
        Nothing ->
          val a = store.list.length
          xmap := xmap.add(x, a)
          a
    fun get-store()
      store
    fun put-store(s)
      store := s
  f()

fun handle-store2(f)
  var store: linearMap<int, abvalue<int>> := get-store()
  var xmap: linearMap<string, int> := linearMap([], fn(s1:string, s2:string) s1 == s2, fn(i1:int, i2:int) i1 == i2, show, show)
  val x = handle({mask behind<estore>{f()}})
    fun ext(a, v)
      store := store.update(a, v, fn(o, n) o.join(n))
    fun alloc(x)
      match xmap.maybeGet(x)
        Just(a) -> a
        Nothing ->
          val a = store.list.length
          xmap := xmap.add(x, a)
          a
    fun get-store() 
      store
    fun put-store(s)
      store := s
  put-store(store)
  x
  

fun evabs(ev0)
  fn (ev)
    fn(e)
      with handleAbsNdet
      with handle-store2
      with handler 
        final ctl fail() injC(ErrorV)
      mask behind<endet>
        // mask behind<estore>
        mask behind<fail>
          ev0(ev)(e)

fun evnormalabs(e)
  fix(evabs(ev'))(e)

fun doevtellabs(e)
  fix(evtell(evabs(ev')))(e)

fun doevdeadabs(e)
  fix(evdead(evabs(ev')))(e)

fun test-abstract(f, e: expr)
  with handleAbsValue
  with default-env
  with handle-store
  with handler 
    final ctl fail() injC(ErrorV)
  with defaultNdet
  f(e)


import expr
import utils
import std/data/linearset
import std/data/linearmap
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

fun lat/show(l: lattice<a>, ?a/show: (a) -> e string): e string
  match l
    Top -> "⊤"
    Bottom -> "⊥"
    Elem(a) -> a.show

fun av/show(a: abvalue<a>, ?a/show: (a) -> <div|e> string): <div|e> string
  a.num.show ++ " {" ++ a.clos.show ++ "}"

fun lat/(==)(l1: lattice<a>, l2: lattice<a>, ?(==): (a, a) -> <div|e> bool): <div|e> bool
  match (l1, l2)
    (Top, Top) -> True
    (Bottom, Bottom) -> True
    (Elem(a1), Elem(a2)) -> a1 == a2
    _ -> False

fun av/(==)(v1: abvalue<a>, v2: abvalue<a>, ?(==): (a, a) -> <div|e> bool): <div|e> bool
  v1.num == v2.num && v1.clos == v2.clos

fun injectConcrete(c: evalue<a>): e abvalue<a>
  match c
    NumV(i) -> Abvalue(Just(Elem(i)), Nothing)
    ClosV(c) -> Abvalue(Nothing, Just(LinearSet([c])))
    ErrorV -> Abvalue(Nothing, Nothing)

fun maybe/join(m1: maybe<a>, m2: maybe<a>, ?join: (a, a) -> e a): e maybe<a>
  match (m1, m2)
    (Just(a1), Just(a2)) -> Just(join(a1, a2))
    (_, Just(a2)) -> Just(a2)
    (Just(a1), _) -> Just(a1)
    (Nothing, Nothing) -> Nothing

fun lat/join(n: lattice<int>, n': lattice<int>): lattice<int>
  match (n, n')
    (Top, _) -> Top
    (_, Top) -> Top
    (Bottom, _) -> n'
    (_, Bottom) -> n
    (Elem(i), Elem(i')) | i == i' -> Elem(i)
    _ -> Top

fun av/join(e: abvalue<a>, e': abvalue<a>, ?(==): (a, a) -> <div|e> bool): <div|e> abvalue<a>
  val num = e.num.join(e'.num)
  val clos = e.clos.join(e'.clos, ?join=fn(s1: linearSet<_>, s2: linearSet<_>) s1.union(s2))
  Abvalue(num, clos)

fun map/join(e: linearMap<int, abvalue<int>>, e': linearMap<int, abvalue<int>>): e linearMap<int,abvalue<int>>
  e'.list.foldl(e) fn(acc, (k1, v1))
    acc.set(k1, v1)

val bottom = Abvalue(Nothing, Nothing)

fun injC(c: evalue<int>): abvalue<int>
  injectConcrete(c)

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
        // _ -> throw("Unknown primitive operation " ++ op ++ " " ++ e0.show ++ " " ++ e1.show)
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
    ctl dereference(m)
      match m
        Just(a) -> match get-store().lookup(a, eq-addr)
          Just(x) -> resume(x)
          Nothing -> throw("Variable " ++ show-addr(a) ++ " not in the store ")
        Nothing -> throw("Unbound variable")

fun handleAbsValue(f)
  handle(f)
    fun inj(e1) injC(e1)
    fun traceR(r: abvalue<int>)
      ("Result: " ++ r.show(showA)).trace
      r
    fun show-addr(a) showA(a)
    fun eq-addr(a1, a2) eqAddr(a1, a2)

val emptyAbsStore : linearMap<int, abvalue<int>> = LinearMap([])

val eqAddr = fn(a: int, b: int) a == b
val showA = fn(i: int) show(i)

fun handle-store(f)
  var store := emptyAbsStore
  var xmap: linearMap<string, int> := LinearMap([])
  with handler
    fun ext(a, v)
      store := store.update(a, v, fn(o, n) o.av/join(n, int/(==)))
    fun alloc(x)
      match xmap.lookup(x)
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
  var xmap: linearMap<string, int> := LinearMap([])
  with return(x)
    put-store(store)
    x
  with override
    fun ext(a, v)
      store := store.update(a, v, fn(o, n) o.av/join(n, int/(==)))
    fun alloc(x)
      match xmap.lookup(x)
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

fun evabs(ev0)
  fn (ev)
    fn(e)
      with handleAbsNdet
      with handler 
        final ctl fail() injC(ErrorV)
      mask behind<endet>
        // mask behind<estore>
        mask behind<fail>
          ev0(ev)(e)

fun evnormalabs(e)
  fix(evabs(ev'))(e)

// fun doevtellabs(e)
//   fix(evtell(evabs(ev')))(e)

// fun doevdeadabs(e)
//   fix(evdead(evabs(ev')))(e)

fun test-abstract(f, e: expr)
  with handleAbsValue
  with default-env
  with handle-store
  with handler 
    final ctl fail() injC(ErrorV)
  with defaultNdet
  f(e)


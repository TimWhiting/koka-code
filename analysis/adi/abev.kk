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

fun show(a: abvalue<a>, showA: (a) -> e string): <div|e> string
  a.num.show(fn(s) s.show(show)) ++ " {" ++ a.clos.show(fn(s) s.list.show-list(fn(c) c.e.show)) ++ "}"

fun show(s: list<(a, abvalue<a>)>, showA: (a) -> <> string): div string
  s.show-list(fn(t) t.show-tuple(showA, fn(s') s'.show(showA)))

fun (==)(l1: lattice<a>, l2: lattice<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  match (l1, l2)
    (Top, Top) -> True
    (Bottom, Bottom) -> True
    (Elem(a1), Elem(a2)) -> eqA(a1, a2)
    _ -> False

fun (==)(v1: abvalue<a>, v2: abvalue<a>, eqA: (a, a) -> <div|e> bool): <div|e> bool
  val numEq = (==)(v1.num, v2.num, fn(a1, a2) (==)(a1, a2, (==)))
  if !numEq then return False
  (==)(v1.clos, v2.clos, fn(m1, m2) m1 == m2)

fun eqStore(s1: linearMap<int, abvalue<int>>, s2: linearMap<int, abvalue<int>>)
  (==)(s1, s2, fn(av1, av2) (==)(av1, av2, (==)))

fun eqConfig(c1: config, c2: config): div bool
  c1.fst == c2.fst && c1.snd == c2.snd && eqStore(c1.thd, c2.thd)

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

val eqAddr = fn(a: int, b: int) a == b
val showA = fn(i: int) show(i)  
val eqAbsV = fn(e1: abvalue<int>, e2: abvalue<int>) (==)(e1, e2, fn(a1, a2) a1 == a2)
val bottom = Abvalue(Nothing, Nothing)

fun handleAbsValue(f)
  handle(f)
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
        ("-", _, _) -> fail()
        ("*", _, _) -> fail()
        ("+", _, _) -> fail()
        ("/", _, _) -> fail()
        _ -> 
          throw("Unknown primitive operation " ++ op ++ " " ++ e0.show(showA) ++ " " ++ e1.show(showA))
    fun zero(v)
      match v
        Abvalue(Just(Elem(0)), _) -> True
        _ -> False
    ctl closures(c)
      match c
        Abvalue(_, Just(c')) -> c'.list.foldl(injectConcrete(ErrorV, eqAddr)) fn(acc:abvalue<int>, c2: clos<env<int>>) 
          acc.join(resume(c2))
        _ -> injectConcrete(ErrorV, eqAddr)
    fun inj(e1)
      injectConcrete(e1, eqAddr)
    fun traceR(r: abvalue<int>)
      r.show(showA).trace
      r
    val show-addr = showA
    val eq-addr = eqAddr

fun handle-store(f)
  var store: linearMap<int, abvalue<int>> := linearMap([], eqAddr)
  var xmap := linearMap([], fn(s1:string, s2:string) s1 == s2)
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
    ctl get(m)
      match m
        Just(a) -> match store.maybeGet(a)
          Just(x) -> resume(x)
          Nothing -> throw("Variable " ++ showA(a) ++ " not in the store " ++ store.show(showA, fn(v) show(v, showA)))
        Nothing -> throw("Unbound variable")
    fun show-store()
      store.show(showA, fn(v) show(v, show)).trace
    fun get-store()
      store
    fun put-store(s)
      store := s
  f()

fun test-abstract(f, e: expr)
  with handler 
    final ctl fail() injectConcrete(ErrorV, eqAddr)
  with handleAbsValue
  with default-env
  with handle-store
  f(e)


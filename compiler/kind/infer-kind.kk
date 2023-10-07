import compiler/lib/pprint
import compiler/common/failure
import compiler/common/id
import compiler/common/nice
import compiler/common/name
import compiler/common/name-prim
import compiler/common/color-scheme
import compiler/common/name-collections
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/pretty
import newstd/data/linearmap
import newstd/data/linearset

// Inference Kind: These kinds contain meta kind variables
type infKind
  KIVar(kid: id)
  KICon(k: kind)
  KIApp(k1: infKind, k2: infKind)

fun (==)(k1: infKind, k2: infKind): div bool
  match (k1, k2)
    (KIVar(kid1), KIVar(kid2)) -> kid1 == kid2
    (KICon(k1), KICon(k2)) -> k1 == k2
    (KIApp(k11, k12), KIApp(k21, k22)) -> k11 == k21 && k12 == k22
    _ -> False

alias infKGamma = linearMap<name, infKind>
val infKGammaEmpty = linearMap([], fn(n1: name, n2: name) n1 == n2, fn(k1: infKind, k2: infKind) k1 == k2, show, show)

val infKindStar = KICon(kindStar)
val infKindHandled = KICon(kindHandled)
val infKindLabel = KICon(kindLabel)
fun infKindFun(k1: infKind, k2: infKind)
  KIApp(KIApp(KICon(kindArrow), k1), k2)

fun infKindFunN(kinds: list<infKind>, k: infKind)
  kinds.foldr(k, infKindFun)

fun isInfKindScope(infk: infKind)
  match infk
    KICon(k) -> k == kindScope
    _ -> False

// Lift KApp nodes to KIApp
fun liftKApp(infkind: infKind)
  match infkind
    KIVar -> infkind
    KIApp(k1, k2) -> KIApp(k1.liftKApp, k2.liftKApp)
    KICon(KCon(_)) -> infkind
    KICon(KApp(k1, k2)) -> KIApp(KICon(k1).liftKApp, KICon(k2).liftKApp)

// extract arguments
fun infExtractKindFun(infkind: infKind)
  fun inj(k1, (ks, _))
    (Cons(k1, ks), k1)
  match infkind
    KIApp(KIApp(KICon(ka), k1), k2) | ka == kindArrow -> k1.inj(k2.infExtractKindFun)
    KIApp(KICon(KApp(ka, k1)), k2) | ka == kindArrow -> KICon(k1).inj(k2.infExtractKindFun)
    KICon(KApp(KApp(ka, k1), k2)) | ka == kindArrow -> KICon(k1).inj(KICon(k2).infExtractKindFun) 
    _ -> ([], infkind)

// Substitution
alias ksub = id-map<infKind>
alias kvs = id-set

val ksubEmpty = linearMap([], fn(id1: id, id2: id) id1 == id2, fn(ik1: infKind, ik2: infKind) ik1 == ik2, show, show)
fun ksubSingle(id: id, infkind: infKind)
  ksubEmpty.add(id, infkind)

fun compose(sub1: ksub, sub2: ksub): ksub
  sub1.union(sub1 |-> sub2)

fun (|->)(sub: ksub, k: infKind): infKind
  match k
    KIVar(kid) -> sub.maybeGet(kid).default(k)
    KIApp(k1, k2) -> KIApp(sub |-> k1, sub |-> k2)
    KICon(k) -> KICon(k)

fun (|->)(sub1: ksub, sub2: ksub): ksub
  sub2.map(fn(k, v) (k, sub1 |-> v))

fun fkv(sub: ksub): pure kvs
  sub.list.map(fn((_, s)) s.fkv).unions

fun fkv(k: infKind): kvs
  match k
    KIVar(kid) -> emptyIds + kid
    KIApp(k1, k2) -> k1.fkv.union(k2.fkv)
    KICon(_) -> emptyIds

// Pretty printing
fun show(infkind: infKind): <compFlags,pure,colorSchemeEffect> string
  with niceKindEnv()
  infkind.fkv.foreach(extendNice)
  infkind.ppInfKind(precInfKindTop).pprint/show

fun niceInfKinds(kinds: list<infKind>)
  with niceKindEnv()
  kinds.map(fkv).unions.list.map(extendNice)
  kinds.map(fn(k) k.liftKApp.ppInfKind(precInfKindTop))

fun ppInfKind(k: infKind, prec: int): <pure, niceEff<id>, compFlags, colorSchemeEffect> doc
  fun collectFunArgs(ik: infKind)
    match ik
      KIApp(KIApp(KICon(KCon(nm)), k1), k2) | nm == "->".newName -> Cons(k1, k2.collectFunArgs)
      _ -> [ik]
  fun collectArgs(ik: infKind)
    match ik
      KIApp(k1, k2) -> k1.collectArgs ++ [k2]
      _ -> [ik]
  match k
    KIVar(id) -> getNiceDoc(id)
    KICon(k') -> k'.ppKind(prec)
    KIApp(KIApp(KICon(KCon(nm)), k1), k2) | nm == nameKindFun ->
      val doc = match k2.collectFunArgs
        [res] -> k1.ppInfKind(precInfKindArrow) |+| "->".text |+| res.ppInfKind(precInfKindArrow - 1)
        Cons(res, args) -> Cons(k1, args).commaParens(fn(p') p'.ppInfKind(precInfKindTop)) |+| "->".text |+| res.ppInfKind(precInfKindArrow - 1)
        _ -> throw("kind/inferKind KIApp function")
      doc.pparens(prec, precInfKindArrow)
    KIApp ->
      val doc = match k.collectArgs
        Cons(k', ks) -> k'.ppInfKind(precInfKindApp - 1) |+| ks.commaParens(fn(p') p'.ppInfKind(precInfKindTop))
        _ -> throw("kind/inferKind KIApp")
      doc.pparens(prec, precInfKindApp)

fun niceKindEnv(f)
  var nice := niceEmpty
  var kindIndex := -1
  with handler
    fun extendNice(k: id)
      kindIndex := kindIndex + 1
      if kindIndex == 0 then
        nice := nice.extend(k, "k")
      else
        nice := nice.extend(k, (kindIndex + 'k'.int).char.string)
      ()
    fun getNice(k: id)
      nice.niceShow(k)
    fun getNiceDoc(k: id)
      nice.nicePretty(k)
  f()

alias prec = int
val precInfKindTop = 0
val precInfKindArrow = 1
val precInfKindApp = 2
val precInfKindAtom = 3
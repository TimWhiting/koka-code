import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/id
import compiler/common/range
import compiler/common/failure
import compiler/kind/kind
import newstd/data/sort
import std/core/unsafe
import std/core/undiv

pub type ktype
  TForAll(vars: list<typeVar>, pred: list<pred>, r: ktype) // rho
  TFun(args: list<(name, ktype)>, e: ktype, t: ktype) // keffect
  TCon(constant: typeCon)
  TVar(variable: typeVar)
  TApp(t: ktype, args: list<ktype>)
  TSyn(syn: typeSyn, args: list<ktype>, t: ktype)

fun ktype/show(tp: ktype): div string
  match tp
    TForAll(vars, preds, t) -> "forall " ++ vars.show-list(show) ++ " . " ++ preds.show-list(show) ++ " => " ++ t.show
    TFun(args, eff, t) -> "(" ++ args.show-list(fn((name, tp1)) name.name/name/show ++ tp1.pretend-decreasing.show) ++ " -> " ++ eff.show ++ " " ++ t.show ++ ")"
    TCon(c) -> c.name.name/name/show
    TVar(v) -> v.tid.show-id
    TApp(t, args) -> t.show ++ " " ++ args.show
    TSyn(syn, args, t) -> syn.name.name/name/show ++ " " ++ args.show ++ " " ++ t.show
  
type pred
  PredSub(a: ktype, b: ktype)
  PredIFace(n: name, tps: list<ktype>) 

fun pred/show(p: pred): div string
  match p
    PredSub(a, b) -> a.show ++ " <: " ++ b.show
    PredIFace(n, tps) -> n.name/name/show ++ " " ++ tps.show

// Various synonyms of types
pub alias scheme = ktype
pub alias sigma = ktype // polymorphic type
pub alias tau = ktype // monomorphic type 
pub alias rho = ktype // unqualified type
pub alias keffect = tau

// An inference type can contain type variables of flavour 'Meta' or 'Skolem'
// pub alias inferType = ktype;

// Variables in a type which have an identifier and kind
// One can ask for the free type variables in a type, and substitute them with 'Tau' types.
pub value struct typeVar
  tid: id
  kind: kind
  flavour: flavour;

fun show(t: typeVar): string
  t.tid.show-id ++ "::" ++ t.kind.show

fun tv/(==)(t1: typeVar, t2: typeVar): bool
  t1.tid == t2.tid

fun tv/cmp(t1: typeVar, t2: typeVar)
  cmp(t1.tid, t2.tid)

// Type constants have a name and a kind
value struct typeCon
  name: name
  kind: kind;

fun typecon/(==)(t1: typeCon, t2: typeCon): bool
  name/(==)(t1.name, t2.name)

fun typecon/cmp(t1: typeCon, t2: typeCon): order
  t1.name.name/name/cmp(t2.name)

// Type synonyms have an identifier, kind, and rank (= partial ordering among type synonyms)
pub struct typeSyn
  name: name
  kind: kind
  rank: synonymRank
  info: maybe<synInfo>

fun typesyn/(==)(t1: typeSyn, t2: typeSyn): bool
  name/(==)(t1.name, t2.name)

fun typesyn/cmp(t1: typeSyn, t2: typeSyn): order
  t1.name.name/name/cmp(t2.name)

// The rank of a type synonym gives a relative ordering among them. This is used
// during unification to increase the chance of matching up type synonyms.
pub alias synonymRank = int


pub fun maxSynonymRank(t: ktype): synonymRank
  fun maxSynonymRanks(tps: list<ktype>): int
    tps.foldr(0) fn(t1, r) 
      max(r, maxSynonymRank(t1.pretend-decreasing))
  match t
    TForAll(_, _, r) -> maxSynonymRank(r.pretend-decreasing)
    TFun(args, eff, ty) -> maxSynonymRanks(Cons(ty, Cons(eff, args.map(fn (f) -> f.snd))).pretend-decreasing)
    TCon(_) -> 0
    TVar(_) -> 0
    TApp(ty, tps) -> maxSynonymRanks(Cons(ty, tps).pretend-decreasing)
    TSyn(syn, args, ty) -> max(syn.rank, maxSynonymRanks(Cons(ty, args).pretend-decreasing))

// Information about types
pub struct dataInfo
  sort: dataKind
  name: name
  kind: kind
  params: list<typeVar>
  constrs: list<conInfo>
  range: range
  def: dataDef
  vis: visibility
  doc: string

fun datainfo/(==)(d1: dataInfo, d2: dataInfo): bool
  name/(==)(d1.name, d2.name)

fun datainfo/show(d: dataInfo): string
  d.name.name/name/show

pub fun is-rec(d: dataInfo): bool
  d.def.is-rec

pub fun is-Open(d: dataInfo): bool
  d.def.is-open

pub fun isLiteral(d: dataInfo): bool
  val n = d.name
  n == nameTpInt || n == nameTpChar || n == nameTpString || n == nameTpFloat

// Constructor information: constructor name, name of the newtype, field types, and the full type of the constructor
pub struct conInfo
  name: name
  typeName: name
  // sort: name
  foralls: list<typeVar> // quantifiers
  existentials: list<typeVar> // existentials
  params: list<(name, ktype)> // field types
  typeScheme: ktype // scheme
  typeSort: dataKind // inductive, coinductive, retractive
  range: range
  paramRanges: list<range>
  paramVis: list<visibility>
  singleton: bool // only constructor of this type
  orderedParams: list<(name, ktype)>
  valueRepr: valueRepr
  vis: visibility
  doc: string;

fun coninfo/(==)(c1: conInfo, c2: conInfo): bool
  name/(==)(c1.name, c2.name)

fun coninfo/show(c: conInfo): string
  c.name.name/name/show

fun coninfo/size(c: conInfo, p: platform)
  syntax/full/size(p, c.valueRepr)

fun scan-count(c: conInfo)
  syntax/scanCount(c.valueRepr)

// A type synonym is quantified by type parameters
pub struct synInfo
  name: name
  kind: kind
  params: list<typeVar> // type parameters
  t: ktype // result type
  rank: synonymRank
  range: range
  pub vis: visibility
  doc: string;

fun syninfo/(==)(s1: synInfo, s2: synInfo): bool
  name/(==)(s1.name, s2.name)

fun syninfo/show(s: synInfo): string
  s.name.name/name/show

fun is-bound(t: typeVar): bool
  t.flavour == Bound

// unifiable
fun is-meta(t: typeVar): bool
  t.flavour == Meta

// not unifiable
fun is-skolem(t: typeVar): bool
  t.flavour == Skolem

fun pred-type(p: pred): exn ktype
  match p
    PredSub(t1, t2) -> TFun([("sub".new-name, t1)], typeTotal, t2)
    PredIFace(_, _) -> todo("type.kk: predType")

fun mustSplit(tp)
  match tp
    TForAll -> True
    TSyn(_, _, tp) -> tp.mustSplit
    _ -> False

fun splitPredType(tp: ktype): (list<typeVar>, list<pred>, rho)
  match tp
    TForAll(vars, preds, t) -> (vars, preds, t)
    _ -> if tp.mustSplit then tp.pretend-decreasing.splitPredType else ([], [], tp)

fun shallowSplitVars(tp: ktype)
  match tp
    TForAll(vars, preds, t) -> (vars, preds, t)
    _ -> ([], [], tp)

fun shallowSplitPreds(tp: ktype)
  match tp
    TForAll(_, preds) -> preds
    _ -> []

fun expandSyn(tp: ktype): ktype
  match tp
    TSyn(_, _, t) -> expandSyn(t)
    _ -> tp

fun canonicalForm(tp: ktype): pure ktype
  match tp
    TSyn(_, _, t) -> canonicalForm(t)
    TForAll(vars, preds, t) -> TForAll(vars, preds, canonicalForm(t))
    TApp(t, ts) -> TApp(canonicalForm(t), ts.map(canonicalForm))
    TFun(args, eff, res) -> TFun(args.map(fn((name, t)) (name, t.canonicalForm)), orderEffect(eff.canonicalForm), res.canonicalForm)
    _ -> tp

// Removes names from function arguments
fun minimalForm(tp: ktype): pure ktype
  match tp
    TSyn -> tp.canonicalForm
    TForAll(vars, preds, t) -> TForAll(vars, preds, t.canonicalForm)
    TApp(t, ts) -> TApp(t.canonicalForm, ts.map(canonicalForm))
    TFun(args, eff, res) -> TFun(args.map(fn((_, t)) (nameNull, t.canonicalForm)), orderEffect(eff.canonicalForm), res.canonicalForm)

// Create a type scheme from a list of quantifiers
fun makeScheme(vars: list<typeVar>, rho: rho): scheme
  val (vars0, preds, _) = rho.splitPredType
  TForAll(vars ++ vars0, preds, rho)

fun quantifyType(vars: list<typeVar>, tp: scheme): scheme
  val (vars0, preds, rho) = tp.splitPredType
  TForAll(vars ++ vars0, preds, rho)

fun qualifyType(preds: list<pred>, tp: scheme): scheme
  val (vars, preds0, rho) = tp.splitPredType
  TForAll(vars, preds ++ preds0, rho)

fun applyType(tp1: ktype, tp2: ktype): ktype
  match tp1
    TApp(tp, tps) -> TApp(tp, tps ++ [tp2])
    TSyn(_, _, tp) | tp.mustSplit -> applyType(tp, tp2)
    _ -> TApp(tp1, [tp2])

fun type-arities(tp: ktype): (int, int)
  match tp.splitFunScheme
    Just((tvars, _, pars, _, _)) -> (tvars.length, pars.length)
    Nothing -> (0, 0)

fun splitFunScheme(tp: scheme): maybe<(list<typeVar>, list<pred>, list<(name, tau)>, keffect, tau)>
  val (tvars, preds, rho) = tp.splitPredType
  match rho.splitFunType
    Just((pars, eff, res)) -> Just((tvars, preds, pars, eff, res))
    Nothing -> Nothing

fun isTVar(tp: ktype): bool
  match tp
    TVar -> True
    TSyn(_, _, t) -> t.isTVar
    _ -> False

fun isTCon(tp: ktype): bool
  match tp
    TCon -> True
    TSyn(_, _, t) -> t.isTCon
    _ -> False

fun isRho(tp: ktype): bool
  match tp
    TForAll -> False
    TSyn(_, _, t) -> t.isRho
    _ -> True

fun isTau(tp: ktype): bool
  match tp
    TForAll -> False
    TFun(xs, e, r) -> xs.all(fn(x) x.snd.pretend-decreasing.isTau) && e.isTau && r.isTau
    TCon -> True
    TVar -> True
    TApp(a, b) -> a.isTau && b.all(fn(x) x.pretend-decreasing.isTau)
    TSyn(_, _, t) -> t.isTau

fun splitFunType(tp: ktype): maybe<(list<(name, ktype)>, ktype, ktype)>
  match tp
    TFun(args, eff, res) -> Just((args, eff, res))
    TSyn(_, _, t) -> t.splitFunType
    _ -> Nothing

// Primitive types
val typeInt = TCon(tconInt)
val tconInt = TypeCon(nameTpInt, kindStar)
fun isTypeInt(t: ktype): bool
  match t
    TCon(c) -> c == tconInt
    _ -> False

val typeInt32 = TCon(TypeCon(nameTpInt32, kindStar))
val typeEvIndex = TSyn(TypeSyn(nameTpEvIndex, kindStar, 0, Nothing), [], typeSSizeT)
val typeSSizeT = TCon(TypeCon(nameTpSSizeT, kindStar))
val typeFloat = TCon(TypeCon(nameTpFloat, kindStar))
val typeChar = TCon(tconChar)
val tconChar = TypeCon(nameTpChar, kindStar)
fun isTypeChar(t: ktype): bool
  match t
    TCon(c) -> c == tconChar
    _ -> False

val typeString = TCon(tconString)
val tconString = TypeCon(nameTpString, kindStar)
fun isTypeString(t: ktype): bool
  match t
    TCon(c) -> c == tconString
    _ -> False

fun typeResumeContext(b: tau, e: keffect, e0: keffect, r: tau): tau
  val tcon = TypeCon(nameTpResumeContext, kind-fun(kindStar, kind-fun(kindEffect, kind-fun(kindEffect, kind-fun(kindStar, kindStar)))))
  TApp(TCon(tcon), [b, e, e0, r])

val typeRef = TCon(TypeCon(nameTpRef, kind-fun(kindHeap, kind-fun(kindStar, kindStar))))
val tconLocalVar = TypeCon(nameTpLocalVar, kind-fun(kindHeap, kind-fun(kindStar, kindStar)))
fun isTypeLocalVar(tp: ktype): bool
  match tp.expandSyn
    TApp(TCon(TypeCon(name)), [_, _]) -> name == nameTpLocalVar
    _ -> False

fun isValueOperation(tp: ktype): bool
  match tp.splitPredType.thd
    TSyn(syn, [_]) -> syn.name == nameTpValueOp
    _ -> False


fun orderEffect(tp: tau): <exn,div> tau
  val (ls, tl) = extractOrderedEffect(tp)
  ls.foldr(tl, effectExtend)

fun extractOrderedEffect(tp: tau): exn (list<tau>, tau)
  val (labs, tl) = extractEffectExtend(tp)
  fun expand(l)
    val (ls, tl') = extractEffectExtend(l)
    if tl'.isEffectEmpty && !ls.is-nil then ls else [l]
  val labss = labs.map(expand).concat
  val slabs = labss.sort-by(fn(l1: tau, l2: tau) -> label-name/cmp(l1.label-name, l2.label-name))
  (slabs, tl)

fun label-name(tp: tau): exn name
  tp.label-name-ex.fst

fun label-name-full(tp: tau): pure name
  val (name, i, _) = tp.label-name-ex
  val ids = i.show-id
  postpend(name, "$" ++ ids)

fun label-name-ex(tp: tau): exn (name, int, list<tau>)
  match tp.expandSyn
    TCon(tc) -> (tc.name, 0, [])
    TApp(TCon(TypeCon(name)), [htp]) | name == nameTpHandled || name == nameTpHandled1 -> htp.pretend-decreasing.label-name-ex
    TApp(TCon(tc), targs as Cons(TVar(TypeVar(id, kind, Skolem)), _)) | kind == kindScope -> (tc.name, id, targs)
    TApp(TCon(tc), targs) -> if (tc.name == nameEffectExtend) then throw("non-expanded type sysnonym used as label") else (tc.name, 0, targs)
    _ -> throw("type/type labelNameEx: label is not a constant")

val typePartial = TApp(tconHandled, [TCon(TypeCon(nameTpPartial, kindHandled))])
val typeLocal = TCon(TypeCon(nameTpLocal, kindLocal))
val tconHandled = TCon(TypeCon(nameTpHandled, kind-fun(kindHandled, kindLabel)))
val tconHandled1 = TCon(TypeCon(nameTpHandled1, kind-fun(kindHandled1, kindLabel)))

fun isAsyncFunction(tp: ktype): pure bool
  val rho = tp.splitPredType.thd
  match rho.splitFunType
    Just((_, eff, _)) ->
      val (ls, _) = eff.extractEffectExtend
      ls.any(isEffectAsync)
    _ -> False

fun isEffectAsync(tp: tau): div bool
  match tp.expandSyn
    TForAll(_, _, rho) -> rho.isEffectAsync
    TFun(_, eff) -> eff.isEffectAsync
    TApp(TCon(TypeCon(name)), [t]) | name == nameTpHandled -> t.isEffectAsync
    TCon(TypeCon(hxName)) -> hxName == nameTpAsync
    _ -> False

fun isEffectTyVar(tp: tau): bool
  match tp
    TVar(v) -> v.kind == kindEffect
    _ -> False

val effectEmpty = TCon(TypeCon(nameEffectEmpty, kindEffect))
fun isEffectEmpty(tp: tau): bool
  match tp.expandSyn
    TCon(tc) -> tc.name == nameEffectEmpty
    _ -> False

fun effectExtendNoDup(label: tau, eff: tau): pure tau
  val (ls, _) = label.extractEffectExtend
  match ls
    Nil ->
      val (els, _) = eff.extractEffectExtend
      if els.any(fn(l) l == label) then eff
      else TApp(TCon(tconEffectExtend), [label, eff])
    _ -> ls.effectExtendNoDups(eff)

fun effectExtendNoDups(labels: list<tau>, eff: tau): pure tau
  labels.foldr(eff, effectExtendNoDup)

fun effectExtend(label: tau, eff: tau): pure tau
  val (ls, _) = label.extractEffectExtend
  match ls
    Nil -> TApp(TCon(tconEffectExtend), [label, eff])
    _ -> effectExtends(ls, eff)

val tconEffectExtend = TypeCon(nameEffectExtend, kind-fun(kindLabel, kind-fun(kindEffect, kindEffect)))

fun effectExtends(labels: list<tau>, eff: tau): pure tau
  match labels
    Cons(lab as TSyn(TypeSyn(_, kind)), _) | eff.isEffectEmpty && kind == kindEffect -> lab
    _ -> labels.foldr(eff, effectExtend)

fun effectFixed(labels: list<tau>): pure tau
  effectExtends(labels, effectEmpty)

fun isEffectFixed(tp: tau): bool
  tp.extractEffectExtend.snd.isEffectEmpty

fun extractEffectExtend(t: tau): (list<tau>, tau)
  fun extractLabel(l: tau): list<tau>
    match l.expandSyn
      TApp(TCon(tc), [_, _]) | tc.name == nameEffectExtend ->
        val (ls, _) = l.pretend-decreasing.extractEffectExtend
        // TODO: Assertion
        ls
      _ -> [l]
  match t.expandSyn
    TApp(TCon(tc), [l, e]) | tc.name == nameEffectExtend ->
      val (ls, tl) = e.pretend-decreasing.extractEffectExtend
      (l.extractLabel ++ ls, tl)
    _ -> ([], t)

fun shallowExtractEffectExtend(t: tau): (list<tau>, tau)
  match t
    TApp(TCon(tc), [l,e]) | tc.name == nameEffectExtend ->
      val (ls, tl) = e.shallowExtractEffectExtend
      (Cons(l, ls), tl)
    _ -> ([], t)

fun shallowEffectExtend(label: tau, eff: tau): pure tau
  // We do not expand type synonyms in the label here by using the 'shallow' version of extract
  // this means that type synonyms of kind E (ie. a fixed effect row) could stay around in
  // the label (which should have kind X).
  // We use this to keep type synonyms around longer -- but during unification we got to be
  // careful to expand such synonyms
  val (ls, _) = label.shallowExtractEffectExtend
  match ls
    Nil -> TApp(TCon(tconEffectExtend), [label, eff])
    _ -> effectExtends(ls, eff)

fun unsafe-type(f: () -> pure tau): tau
  unsafe-total
    try(f) fn(e)
      TCon(TypeCon("error".new-name, kindStar))

val typeDivergent = unsafe-type({singleEff(nameTpDiv)})
fun singleEff(nm:name)
  effectExtend(TCon(TypeCon(nm, kindEffect)), effectEmpty)
val typeTotal = TCon(tconTotal)
val tconTotal = TypeCon(nameEffectEmpty, kindEffect)

fun isTypeTotal(t: tau): bool
  match t
    TCon(c) -> c == tconTotal
    _ -> False

val typePure = unsafe-type({effectFixed([typePartial, typeDivergent])})
val typeBool = TCon(tconBool)
fun isTypeBool(t: tau): bool
  match t
    TCon(c) -> c == tconBool
    _ -> False
val tconBool = TypeCon(nameTpBool, kindStar)
fun isTypeUnit(t: tau): bool
  match t
    TCon(c) -> c == tconUnit
    _ -> False
fun typeCCtx(tp: tau)
  TSyn(tsynCCtx, [tp], TApp(typeCCtxx, [tp, tp]))
val tsynCCtx = TypeSyn(nameTpCCtx, kind-fun(kindStar, kindStar), 0, Nothing)
val typeCCtxx = TCon(tconCCtxx)
val tconCCtxx = TypeCon(nameTpCCtxx, kind-fun(kindStar, kind-fun(kindStar, kindStar)))
val typeFieldAddr = TCon(tconFieldAddr)
val tconFieldAddr = TypeCon(nameTpFieldAddr, kind-fun(kindStar, kindStar))
val typeVector = TCon(TypeCon(nameTpVector, kind-fun(kindStar, kindStar)))
val typeList = TCon(tconList)
val tconList = TypeCon(nameTpList, kind-fun(kindStar, kindStar))

val typeEv = TCon(tconEv)
val tconEv = TypeCon(nameTpEv, kind-fun(kindStar, kindStar))
fun isEvType(tp: tau): bool
  match tp
    TCon(c) -> c == tconEv
    _ -> False
fun makeEvType(arg: tau): tau
  typeApp(typeEv, [arg])
fun typeApp(tau: tau, args: list<tau>): tau
  match args
    Nil -> tau
    _ -> match tau
      TApp(tau', ts0) -> TApp(tau', ts0 ++ args)
      _ -> TApp(tau, args)

val typeUnit = TCon(tconUnit)
val tconUnit = TypeCon(nameTpUnit, kindStar)
val typeVoid = TCon(TypeCon(nameTpVoid, kindStar))
val typeReuse = TCon(TypeCon(nameTpReuse, kindStar))
val typeAny = TCon(TypeCon(nameTpAny, kindStar))
fun typeMakeTuple(tps)
  match tps
    Nil -> typeUnit
    [tp] -> tp
    _ -> typeApp(typeTuple(tps.length), tps)

fun typeTuple(n: int)
  TCon(TypeCon(name-tuple(n), kind-fun-n(kindStar.replicate(n), kindStar)))
val typeOptional = TCon(tconOptional)
val tconOptional = TypeCon(nameTpOptional, kind-fun(kindStar, kindStar))
fun isOptional(tp: ktype): bool
  match tp.expandSyn
    TApp(TCon(tc), [_]) -> tc == tconOptional
    _ -> False
fun makeOptionalType(tp: ktype): ktype
  TApp(typeOptional, [tp])

fun unOptional(tp: ktype): ktype
  match tp.expandSyn
    TApp(TCon(tc), [t]) | tc == tconOptional -> t
    _ -> tp

fun pruneSyn(rho: rho): rho
  match rho
    TSyn(_, _, t) -> t.pruneSyn
    TApp(t1, ts) -> TApp(t1.pruneSyn, ts.map(fn(x) x.pretend-decreasing.pruneSyn))
    _ -> rho

fun tv/to-type(v: typeVar)
  TVar(v)

fun tcon/to-type(c: typeCon)
  TCon(c)

fun ktype/(==)(t1: ktype, t2: ktype): pure bool
  match-type(t1, t2)

fun pred/(==)(p1: pred, p2: pred): pure bool
  match-pred(p1, p2)

fun preds/(==)(p1: list<pred>, p2: list<pred>): pure bool
  match-preds(p1, p2)

fun match-type(tp1: ktype, tp2: ktype)
  match (tp1.expandSyn, tp2.expandSyn)
    (TForAll(vs1, ps1, t1), TForAll(vs2, ps2, t2)) -> vs1.zipwith(vs2, (==)).all(id) && match-preds(ps1, ps2) && match-type(t1, t2)
    (TFun(pars1, eff1, res1), TFun(pars2, eff2, res2)) -> pars1.zipwith(pars2, fn(a, b) a.fst == b.fst && a.snd == b.snd).all(id) && eff1 == eff2 && res1 == res2
    (TCon(c1), TCon(c2)) -> c1 == c2
    (TVar(v1), TVar(v2)) -> v1 == v2
    (TApp(t1, ts1), TApp(t2, ts2)) -> t1 == t2 && ts1 == ts2
    _ -> False

fun match-effect(eff1: tau, eff2: tau): pure bool
  match-type(eff1.orderEffect, eff2.orderEffect)

fun ktypes/(==)(l1: list<ktype>, l2: list<ktype>): pure bool
  l1.zipwith(l2, match-type).all(id)

fun match-preds(l1: list<pred>, l2: list<pred>): pure bool
  l1.zipwith(l2, match-pred).all(id)

fun match-pred(p1: pred, p2: pred): pure bool
  match (p1, p2)
    (PredSub(sub1, sup1), PredSub(sub2, sup2)) -> match-type(sub1, sub2) && match-type(sup1, sup2)
    (PredIFace(n1, tps1), PredIFace(n2, tps2)) -> n1 == n2 && tps1 == tps2
    _ -> False
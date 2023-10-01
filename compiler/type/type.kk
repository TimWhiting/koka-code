import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/id
import compiler/common/range
import compiler/common/failure
import compiler/kind/kind
import compiler/type/kind
import newstd/data/sort

pub type ktype
  TForAll(vars: list<typeVar>, pred: list<pred>, r: ktype) // rho
  TFun(args: list<(name, ktype)>, e: ktype, t: ktype) // keffect
  TCon(constant: typeCon)
  TVar(variable: typeVar)
  TApp(t: ktype, args: list<ktype>)
  TSyn(syn: typeSyn, args: list<ktype>, t: ktype)

fun show(tps: list<ktype>): div string
  tps.show-list(show)

fun show(tp: ktype): div string
  match tp
    TForAll(vars, preds, t) -> "forall " ++ vars.show-list(show) ++ " . " ++ preds.show-list(show) ++ " => " ++ t.show
    TFun(args, eff, t) -> "(" ++ args.show-list(fn((name, tp1)) name.show ++ tp1.unsafe-decreasing.show) ++ " -> " ++ eff.show ++ " " ++ t.show ++ ")"
    TCon(c) -> c.name.show
    TVar(v) -> v.tid.show
    TApp(t, args) -> t.show ++ " " ++ args.show
    TSyn(syn, args, t) -> syn.name.show ++ " " ++ args.show ++ " " ++ t.show

type pred
  PredSub(a: ktype, b: ktype)
  PredIFace(n: name, tps: list<ktype>)

fun show(p: pred): div string
  match p
    PredSub(a, b) -> a.show ++ " <: " ++ b.show
    PredIFace(n, tps) -> n.show ++ " " ++ tps.show

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
  t.tid.show ++ "::" ++ t.kind.show

fun (==)(t1: typeVar, t2: typeVar): bool
  t1.tid == t2.tid

fun (<)(t1: typeVar, t2: typeVar)
   core/(<)(t1.tid, t2.tid)

// Type constants have a name and a kind
value struct typeCon
  name: name
  kind: kind;

fun (==)(t1: typeCon, t2: typeCon): bool
  name/(==)(t1.name, t2.name)

fun (<)(t1: typeCon, t2: typeCon): bool
  t1.name.compare(t2.name) == Lt

// Type synonyms have an identifier, kind, and rank (= partial ordering among type synonyms)
pub struct typeSyn
  name: name
  kind: kind
  rank: synonymRank
  info: maybe<synInfo>

fun (==)(t1: typeSyn, t2: typeSyn): bool
  name/(==)(t1.name, t2.name)

fun (<)(t1: typeSyn, t2: typeSyn): bool
  t1.name.compare(t2.name) == Lt

// The rank of a type synonym gives a relative ordering among them. This is used
// during unification to increase the chance of matching up type synonyms.
pub alias synonymRank = int


pub fun maxSynonymRank(t: ktype): synonymRank
  fun maxSynonymRanks(tps: list<ktype>): int
    tps.foldr(0) fn(t1, r) 
      max(r, maxSynonymRank(t1.unsafe-decreasing))
  match t
    TForAll(_, _, r) -> maxSynonymRank(r.unsafe-decreasing)
    TFun(args, eff, ty) -> maxSynonymRanks(Cons(ty, Cons(eff, args.map(fn (f) -> f.snd))).unsafe-decreasing)
    TCon(_) -> 0
    TVar(_) -> 0
    TApp(ty, tps) -> maxSynonymRanks(Cons(ty, tps).unsafe-decreasing)
    TSyn(syn, args, ty) -> max(syn.rank, maxSynonymRanks(Cons(ty, args).unsafe-decreasing))

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

fun (==)(d1: dataInfo, d2: dataInfo): bool
  name/(==)(d1.name, d2.name)

fun show(d: dataInfo): string
  d.name.show

pub fun isRec(d: dataInfo): bool
  d.def.isRec

pub fun isOpen(d: dataInfo): bool
  d.def.isOpen

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

fun (==)(c1: conInfo, c2: conInfo): bool
  name/(==)(c1.name, c2.name)

fun show(c: conInfo): string
  c.name.show

fun size(c: conInfo, p: platform)
  syntax/size(p, c.valueRepr)

fun scanCount(c: conInfo)
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

fun (==)(s1: synInfo, s2: synInfo): bool
  name/(==)(s1.name, s2.name)

fun show(s: synInfo): string
  s.name.show

fun isBound(t: typeVar): bool
  t.flavour == Bound

// unifiable
fun isMeta(t: typeVar): bool
  t.flavour == Meta

// not unifiable
fun isSkolem(t: typeVar): bool
  t.flavour == Skolem

fun predType(p: pred): compilerEff ktype
  match p
    PredSub(t1, t2) -> TFun([("sub".newName, t1)], typeTotal, t2)
    PredIFace(_, _) -> todo("type.kk: predType")

fun mustSplit(tp)
  match tp
    TForAll -> True
    TSyn(_, _, tp) -> tp.mustSplit
    _ -> False

fun splitPredType(tp: ktype): (list<typeVar>, list<pred>, rho)
  match tp
    TForAll(vars, preds, t) -> (vars, preds, t)
    _ -> if tp.mustSplit then tp.unsafe-decreasing.splitPredType else ([], [], tp)

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

fun typeArities(tp: ktype): (int, int)
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
    TFun(xs, e, r) -> xs.all(fn(x) x.snd.unsafe-decreasing.isTau) && e.isTau && r.isTau
    TCon -> True
    TVar -> True
    TApp(a, b) -> a.isTau && b.all(fn(x) x.unsafe-decreasing.isTau)
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
  val tcon = TypeCon(nameTpResumeContext, kindFun(kindStar, kindFun(kindEffect, kindFun(kindEffect, kindFun(kindStar, kindStar)))))
  TApp(TCon(tcon), [b, e, e0, r])

val typeRef = TCon(TypeCon(nameTpRef, kindFun(kindHeap, kindFun(kindStar, kindStar))))
val tconLocalVar = TypeCon(nameTpLocalVar, kindFun(kindHeap, kindFun(kindStar, kindStar)))
fun isTypeLocalVar(tp: ktype): bool
  match tp.expandSyn
    TApp(TCon(TypeCon(name)), [_, _]) -> name == nameTpLocalVar
    _ -> False

fun isValueOperation(tp: ktype): bool
  match tp.splitPredType.thd
    TSyn(syn, [_]) -> syn.name == nameTpValueOp
    _ -> False


fun orderEffect(tp: tau): exn tau
  val (ls, tl) = extractOrderedEffect(tp)
  unsafe-no-div
    ls.foldr(tl, effectExtend)

fun extractOrderedEffect(tp: tau): exn (list<tau>, tau)
  val (labs, tl) = extractEffectExtend(tp)
  fun expand(l)
    val (ls, tl') = extractEffectExtend(l)
    if tl'.isEffectEmpty && !ls.is-nil then ls else [l]
  val labss = labs.map(expand).concat
  val slabs = labss.sortBy(fn(l1: tau, l2: tau) -> labelNameCompare(l1.labelName, l2.labelName))
  (slabs, tl)

fun labelName(tp: tau): exn name
  tp.labelNameEx.fst

fun labelNameFull(tp: tau): pure name
  val (name, i, _) = tp.labelNameEx
  postpend("$" ++ i.show, name)

fun labelNameEx(tp: tau): exn (name, int, list<tau>)
  match tp.expandSyn
    TCon(tc) -> (tc.name, 0, [])
    TApp(TCon(TypeCon(name)), [htp]) | name == nameTpHandled || name == nameTpHandled1 -> htp.unsafe-decreasing.labelNameEx
    TApp(TCon(tc), targs as Cons(TVar(TypeVar(id, kind, Skolem)), _)) | kind == kindScope -> (tc.name, id, targs)
    TApp(TCon(tc), targs) -> if (tc.name == nameEffectExtend) then throw("non-expanded type sysnonym used as label") else (tc.name, 0, targs)
    _ -> throw("type/type labelNameEx: label is not a constant")

val typePartial = TApp(tconHandled, [TCon(TypeCon(nameTpPartial, kindHandled))])
val typeLocal = TCon(TypeCon(nameTpLocal, kindLocal))
val typeCps = TApp(tconHandled, [TCon(TypeCon(nameTpCps, kindHandled))])
val tconHandled = TCon(TypeCon(nameTpHandled, kindFun(kindHandled, kindLabel)))
val tconHandled1 = TCon(TypeCon(nameTpHandled1, kindFun(kindHandled1, kindLabel)))

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

val tconEffectExtend = TypeCon(nameEffectExtend, kindFun(kindLabel, kindFun(kindEffect, kindEffect)))

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
        val (ls, _) = l.unsafe-decreasing.extractEffectExtend
        // TODO: Assertion
        ls
      _ -> [l]
  match t.expandSyn
    TApp(TCon(tc), [l, e]) | tc.name == nameEffectExtend ->
      val (ls, tl) = e.unsafe-decreasing.extractEffectExtend
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
      TCon(TypeCon("error".newName, kindStar))

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
val tsynCCtx = TypeSyn(nameTpCCtx, kindFun(kindStar, kindStar), 0, Nothing)
val typeCCtxx = TCon(tconCCtxx)
val tconCCtxx = TypeCon(nameTpCCtxx, kindFun(kindStar, kindFun(kindStar, kindStar)))
val typeFieldAddr = TCon(tconFieldAddr)
val tconFieldAddr = TypeCon(nameTpFieldAddr, kindFun(kindStar, kindStar))
val typeVector = TCon(TypeCon(nameTpVector, kindFun(kindStar, kindStar)))
val typeList = TCon(tconList)
val tconList = TypeCon(nameTpList, kindFun(kindStar, kindStar))
fun typeNull(tp: tau): tau
  typeApp(TCon(TypeCon(nameTpNull, kindStar)), [tp])

val typeEv = TCon(tconEv)
val tconEv = TypeCon(nameTpEv, kindFun(kindStar, kindStar))
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
  TCon(TypeCon(nameTuple(n), kindFunN(kindStar.replicate(n), kindStar)))
val typeOptional = TCon(tconOptional)
val tconOptional = TypeCon(nameTpOptional, kindFun(kindStar, kindStar))
fun isOptional(tp: ktype): bool
  match tp.expandSyn
    TApp(TCon(tc), [_]) -> tc == tconOptional
    _ -> False
fun makeOptional(tp: ktype): ktype
  TApp(typeOptional, [tp])

fun unOptional(tp: ktype): ktype
  match tp.expandSyn
    TApp(TCon(tc), [t]) | tc == tconOptional -> t
    _ -> tp

fun pruneSyn(rho: rho): rho
  match rho
    TSyn(_, _, t) -> t.pruneSyn
    TApp(t1, ts) -> TApp(t1.pruneSyn, ts.map(fn(x) x.unsafe-decreasing.pruneSyn))
    _ -> rho

fun toType(v: typeVar)
  TVar(v)

fun toType(c: typeCon)
  TCon(c)

fun (==)(t1: ktype, t2: ktype): pure bool
  matchType(t1, t2)

fun (==)(p1: pred, p2: pred): pure bool
  matchPred(p1, p2)

fun matchType(tp1: ktype, tp2: ktype)
  match (tp1.expandSyn, tp2.expandSyn)
    (TForAll(vs1, ps1, t1), TForAll(vs2, ps2, t2)) -> vs1.zipwith(vs2, (==)).all(id) && matchPreds(ps1, ps2) && matchType(t1, t2)
    (TFun(pars1, eff1, res1), TFun(pars2, eff2, res2)) -> pars1.zipwith(pars2, fn(a, b) a.fst == b.fst && a.snd == b.snd).all(id) && eff1 == eff2 && res1 == res2
    (TCon(c1), TCon(c2)) -> c1 == c2
    (TVar(v1), TVar(v2)) -> v1 == v2
    (TApp(t1, ts1), TApp(t2, ts2)) -> t1 == t2 && ts1 == ts2
    _ -> False

fun matchEffect(eff1: tau, eff2: tau): pure bool
  matchType(eff1.orderEffect, eff2.orderEffect)

fun (==)(l1: list<ktype>, l2: list<ktype>): pure bool
  l1.zipwith(l2, matchType).all(id)

fun matchPreds(l1: list<pred>, l2: list<pred>): pure bool
  l1.zipwith(l2, matchPred).all(id)

fun matchPred(p1: pred, p2: pred): pure bool
  match (p1, p2)
    (PredSub(sub1, sup1), PredSub(sub2, sup2)) -> matchType(sub1, sub2) && matchType(sup1, sup2)
    (PredIFace(n1, tps1), PredIFace(n2, tps2)) -> n1 == n2 && tps1 == tps2
    _ -> False
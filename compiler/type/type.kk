import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/id
import compiler/common/range
import compiler/common/failure
import compiler/kind/kind
import newstd/data/sort

pub type ktype
  TForAll(vars: list<typeVar>, pred: list<pred>, r: ktype) // rho
  TFun(args: list<(name, ktype)>, e: ktype, t: ktype) // keffect
  TCon(constant: typeCon)
  TVar(variable: typeVar)
  TApp(t: ktype, args: list<ktype>)
  TSyn(syn: typeSyn, args: list<ktype>, t: ktype)

type pred
  PredSub(a: ktype, b: ktype)
  PredIFace(n: name, tps: list<ktype>)

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

fun (==)(t1: typeVar, t2: typeVar): bool
  id/(==)(t1.tid, t2.tid)

fun (<)(t1: typeVar, t2: typeVar)
  id/(<)(t1.tid, t2.tid)

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
  vis: visibility
  doc: string;

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
    PredSub(t1, t2) -> typeFun([("sub".newName, t1)], typeTotal, t2)
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

fun canonicalForm(tp: ktype): ktype
  match tp
    TSyn(_, _, t) -> canonicalForm(t)
    TForAll(vars, preds, t) -> TForAll(vars, preds, canonicalForm(t))
    TApp(t, ts) -> TApp(canonicalForm(t), ts.map(canonicalForm))
    TFun(args, eff, res) -> TFun(args.map(fn((name, t)) (name, t.canonicalForm)), orderEffect(eff.canonicalForm), res.canonicalForm)
    _ -> tp

// Removes names from function arguments
fun minimalForm(tp: ktype): ktype
  match tp
    TSyn -> t.canonicalForm
    TForAll(vars, preds, t) -> TForAll(vars, preds, t.canonicalForm)
    TApp(t, ts) -> TApp(t.canonicalForm, ts.map(canonicalForm))
    TFun(args, eff, res) -> TFun(args.map(fn((name, t)) (nameNull, t.canonicalForm)), orderEffect(eff.canonicalForm), res.canonicalForm)

// TODO:

fun typeFun(args: list<(name, ktype)>, eff: ktype, res: ktype): ktype
  TFun(args, eff, res)


val typeTotal = TCon(tconTotal)
val tconTotal = TypeCon(nameEffectEmpty, kindEffect)

fun isTypeTotal(t: tau): bool
  match t
    TCon(c) -> c == tconTotal
    _ -> False

// val typePure = effectFixed([typePartial, typeDivergent])

val effectEmpty = TCon(TypeCon(nameEffectEmpty, kindEffect))
fun isEffectEmpty(tp: tau): bool
  match tp.expandSyn
    TCon(tc) -> tc.name == nameEffectEmpty
    _ -> False

// TODO

fun orderEffect(tp: tau): tau
  val (ls, tl) = extractOrderedEffect(tp)
  foldr(effectExtend, tl, ls)

fun extractOrderedEffect(tp: tau): (list<tau>, tau)
  val (labs, tl) = extractEffectExtend(tp)
  fun expand(l)
    val (ls, tl') = extractEffectExtend(l)
    if tl'.isEffectEmpty && !ls.is-nil then ls else [l]
  val labss = labs.map(expand).concat
  val slabs = labss.sortBy(fn(l1: tau, l2: tau) -> labelNameCompare(l1.name, l2.name))
  (slabs, tl)

fun labelName(tp: tau): name
  tp.labelNameEx.fst

fun labelNameFull(tp: tau): name
  val (name, i, _) = tp.labelNameEx
  postpend("$" ++ i.show, name)

fun labelNameEx(tp: tau): (name, int, list<tau>)
  match tp.expandSyn
    TCon(tc) -> (tc.name, 0, [])
    TApp(TCon(TypeCon(name)), [htp]) | name == nameTpHandled || name == nameTpHandled1 -> htp.labelNameEx
    TApp(TCon(tc), Cons(TVar(TypeVar(id, kind, Skolem)), _)) -> 
// TODO:


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

    



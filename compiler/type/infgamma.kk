

import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/common/color-scheme
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import compiler/lib/pprint
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/assumption
import std/data/linearmap

pub infixr 5 (|->)
// inf gamma
// Environment mapping names to type schemes. Due to overloading
// there may be multiple entries for the same name
alias infGamma = name-map<list<nameInfo>>

effect infGammaEff
  fun infGammaExtend(name: name, ni: nameInfo): ()
  fun infGammaLookupX(name: name): maybe<nameInfo>
  fun infGammaSet(inf: infGamma): ()
  fun infGammaGet(): infGamma

fun inf-gamma(ig0: infGamma, f: () -> <infGammaEff,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var ig := ig0
  with handler
    fun infGammaExtend(name: name, ni: nameInfo) ig := ig.extend(name, ni)
    fun infGammaLookupX(name: name) Nothing // ig.lookup(name)
    fun infGammaSet(inf: infGamma) ig := inf
    fun infGammaGet() ig
  f()

fun ni/combine(nis: list<nameInfo>, nis2: list<nameInfo>): exn list<nameInfo>
  match nis
    [] -> nis2
    Cons(ni, nis) -> combine(nis, Cons(ni, nis2.filter(fn(ni2) ni.cname != ni2.cname)))

// TODO: Update
// note: qualified names can get inserted into gamma due to recursive definitions, or
// during inference by inserting fully qualified expressions (in resolveAppName)
// (if isQualified name then trace ("infGammaExtend: insert qualified: " ++ show name) else id) $
// overwrite previous names
fun inf-gamma/extend(ig: infGamma, name: name, ni: nameInfo): <exn> infGamma
  ig.update(name.unqualify, [ni], ni/combine)

fun inf-gamma-eff/extends(tnames: list<(name,ktype,string)>)
  tnames.foreach(fn((name,tp,doc)) extend-tp(name, name, tp, doc))
fun inf-gamma/extends(ig: infGamma, tnames: list<(name,ktype,string)>)
  tnames.foldl(ig, fn(ig', (name,tp,doc)) ig'.extend-tp(name, name, tp, doc))

fun inf-gamma-eff/extend-tp(name: name, cname: name, tp: ktype, doc: string)
  extend-x(name, cname, tp, range/range/null, False, doc)
fun inf-gamma/extend-tp(ig: infGamma, name: name, cname: name, tp: ktype, doc: string)
  ig.extend-x(name, cname, tp, range/range/null, False, doc)

fun inf-gamma-eff/extend-x(name: name, cname: name, tp: ktype, rng: range, isVar: bool, doc: string)
  infGammaExtend(name, InfoVal(Public, cname, tp, rng, isVar, doc))
fun inf-gamma/extend-x(ig: infGamma, name: name, cname: name, tp: ktype, rng: range, isVar: bool, doc: string)
  ig.set(name, InfoVal(Public, cname, tp, rng, isVar, doc))

// fun inf-gamma-eff/lookup(name: name): <infGammaEff,exn> maybe<(name,ktype)>
//   infGammaLookupX(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))
// fun inf-gamma/lookup(ig: infGamma, name: name): exn maybe<(name, ktype)>
//   ig.lookup(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))

fun inf-gamma/list(ig: infGamma): pure list<(name, ktype)>
  ig.list.map(fn((name, InfoVal(typ=tp))) (name, tp))

fun inf-gamma-eff/list()
  infGammaGet().list.map(fn((name, InfoVal(typ=tp))) (name, tp))

val inf-gamma/empty: infGamma = LinearMap([])

fun (|->)(sub: sub, inf: infGamma): pure infGamma
  inf.map(fn(k, ni) (k, sub |-> ni))

fun ppInfGamma(ig: infGamma)
  val nameSchemes = ig.infGammaList()
  val maxWidth = nameSchemes.map(fn((n, _)) n.show.count).maximum(0).min(12)
  fun nice(scheme: ktype)
    align(niceTypes([scheme]).head.unjust)
  vcat(nameSchemes.map(fn((n, s))
    fill(n.showPlain.text |.| typeColon().color(colors.colorSep) |+| align(nice(s)), maxWidth)
  ))

fun pretty(ig: infGamma)
  // TODO: Add default env to pretty definitions?
  ppInfGamma(ig)

fun showInfGamma(ig: infGamma)
  pretty(ig).show
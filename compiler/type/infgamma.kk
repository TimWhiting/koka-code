

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
import newstd/data/linearmap

pub infixr 5 (|->)
// inf gamma
// Environment mapping names to type schemes. Due to overloading
// there may be multiple entries for the same name
alias infGamma = name-map<nameInfo>

effect infGammaEff
  fun infGammaExtend(name: name, ni: nameInfo): ()
  fun infGammaLookupX(name: name): maybe<nameInfo>
  fun infGammaSet(inf: infGamma): ()
  fun infGammaGet(): infGamma

fun withinfGamma(ig0: infGamma, f: () -> <infGammaEff,exn,compFlags|e> a): <exn,compFlags|e> a
  var ig := ig0
  with handler
    fun infGammaExtend(name: name, ni: nameInfo) ig := infGammaExtend(ig, name, ni)
    fun infGammaLookupX(name: name) infGammaLookupX(ig, name)
    fun infGammaSet(inf: infGamma) ig := inf
    fun infGammaGet() ig
  f()

fun infGammaUnions(ks: list<infGamma>)
  unions(ks)
fun infGammaExtend(ig: infGamma, name: name, ni: nameInfo)
  ig.set(name.unqualify, ni)
fun infGammaLookupX(ig: infGamma, name: name): maybe<nameInfo>
  ig.maybeGet(name)

fun infGammaLookup(name: name)
  infGammaLookupX(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))
fun infGammaLookup(ig: infGamma, name: name): exn maybe<(name, ktype)>
  ig.infGammaLookupX(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))

fun infGammaExtendTp(name: name, cname: name, tp: ktype)
  infGammaExtendX(name, cname, tp, rangeNull, False)
fun infGammaExtendTp(ig: infGamma, name: name, cname: name, tp: ktype)
  ig.infGammaExtendX(name, cname, tp, rangeNull, False)
fun infGammaExtendX(name: name, cname: name, tp: ktype, rng: range, isVar: bool)
  infGammaExtend(name, InfoVal(Public, cname, tp, rng, isVar))
fun infGammaExtendX(ig: infGamma, name: name, cname: name, tp: ktype, rng: range, isVar: bool)
  ig.set(name, InfoVal(Public, cname, tp, rng, isVar))
fun infGammaExtends(ig: infGamma, tnames: list<(name,ktype)>)
  tnames.foldl(ig, fn(ig', (name,tp)) infGammaExtendTp(ig', name, name, tp))
fun infGammaExtends(tnames: list<(name,ktype)>)
  tnames.foreach(fn((name,tp)) infGammaExtendTp(name, name, tp))

fun infGammaList(ig: infGamma): pure list<(name, ktype)>
  ig.list.map(fn((name, InfoVal(typ=tp))) (name, tp))

fun infGammaList()
  infGammaGet().list.map(fn((name, InfoVal(typ=tp))) (name, tp))

val eqK = fn(ni1:nameInfo, ni2:nameInfo) ni1 == ni2
val showK = fn(ni:nameInfo) ni.show

val emptyInfGamma = linearMap([], fn(n1, n2: name) n1 == n2, eqK, show, showK)

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
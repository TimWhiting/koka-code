import kind
import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearmap

alias kGamma = qname-map<kind>

effect kGammaEff
  fun kgammaExtend(name: name, k: kind): ()
  fun kgammaLookup(ctxt: name, name: name): lookup<kind>
  fun kgammaLookupQ(name: name): maybe<kind>
  fun kgammaFind(ctxt: name, name: name): (name, kind)
  fun kgammaList(): list<(name, list<(name, kind)>)>
  fun kgammaFilter(modName: name): kGamma

fun withKGamma(kg0: kGamma, f: () -> <kGammaEff,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var kg := kg0
  with handler
    fun kgammaExtend(name: name, k: kind) kg := kgammaExtend(kg, name, k)
    fun kgammaLookup(ctxt, name: name) kg.kgammaLookup(ctxt, name)
    fun kgammaLookupQ(name: name) kg.kgammaLookupQ(name)
    fun kgammaFind(ctxt: name, name: name) kg.kgammaFind(ctxt, name)
    fun kgammaList() kg.list
    fun kgammaFilter(modName: name) kg.kgammaFilter(modName)
  f()

fun kgammaUnions(ks: list<kGamma>)
  unions(ks)
fun kgammaNewNub(xs: list<(name,kind)>): <comp-flags, exn> kGamma
  xs.foldl(emptyKGamma, fn(m, (n,k)) m.insert(n,k))
fun kgammaExtend(kg: kGamma, name: name, k: kind)
  kg.insert(name, k)
fun kgammaLookup(kg: kGamma, ctxt:name , name: name)
  kg.lookup(ctxt, name)
fun kgammaLookupQ(kg: kGamma, name: name)
  kg.lookupQ(name)
fun kgammaFind(kg: kGamma, ctxt: name, name: name)
  match kg.lookup(ctxt, name)
    Found((qn, scheme)) -> (qn, scheme)
    _ -> fail("kind lookup failed")
fun kgammaFilter(kg: kGamma, modName: name)
  kg.filterNames(fn(n) n == modName)

val eqK = fn(k1:kind, k2:kind) k1 == k2
val showK = fn(k:kind) k.show
fun single(name: name, k: kind): kGamma
  name-collections/single(name, k, eqK, showK)

val emptyKGamma = qname-empty(eqK, showK)

fun extractKGamma(c: core): <exn,comp-flags> kGamma
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <exn,comp-flags> kGamma
  g.map(extractTypeDef).unions

fun extractTypeDef(d: typeDef): kGamma
  match d
    Synonym(synInfo) | synInfo.vis.is-public -> single(synInfo.name, synInfo.kind)
    Data(dataInfo, False) | dataInfo.vis.is-public -> single(dataInfo.name, dataInfo.kind)
    _ -> emptyKGamma

// TODO: Pretty print
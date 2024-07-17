import compiler/kind/kind
import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap

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
    fun kgammaExtend(name: name, k: kind) kg := kg.extend(name, k)
    fun kgammaLookup(ctxt, name: name) kg.lookup(ctxt, name)
    fun kgammaLookupQ(name: name) kg.lookup-qualified(name)
    fun kgammaFind(ctxt: name, name: name) kg.find(ctxt, name)
    fun kgammaList() kg.list
    fun kgammaFilter(modName: name) kg.filter(modName)
  f()

fun kgamma/new-nub(xs: list<(name,kind)>): <comp-flags, exn> kGamma
  xs.foldl(empty, fn(m, (n,k)) m.insert(n,k))
fun kgamma/extend(kg: kGamma, name: name, k: kind)
  kg.insert(name, k)
fun kgamma/find(kg: kGamma, ctxt: name, name: name)
  match kg.lookup(ctxt, name)
    Found((qn, scheme)) -> (qn, scheme)
    _ -> fail("kind lookup failed")
fun kgamma/filter(kg: kGamma, modName: name)
  kg.filter-names(fn(n) n == modName)

val kgamma/empty:kGamma = LinearMap([])

fun core/extract-typedefs(c: core): <exn,comp-flags> kGamma
  c.typeDefs.map(extract-typedefs).unions

fun tdg/extract-typedefs(g: typeDefGroup): <exn,comp-flags> kGamma
  g.map(extract-typedefs).unions

fun td/extract-typedefs(d: typeDef): kGamma
  match d
    Synonym(synInfo) | synInfo.vis.is-public -> single(synInfo.name, synInfo.kind)
    Data(dataInfo, False) | dataInfo.vis.is-public -> single(dataInfo.name, dataInfo.kind)
    _ -> kgamma/empty

// TODO: Pretty print
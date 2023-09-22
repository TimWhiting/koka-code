import kind
import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearmap

effect kGamma
  fun kgammaExtend(name: name, k: kind): ()
  fun kgammaLookup(ctxt: name, name: name): lookup<kind>
  fun kgammaLookupQ(name: name): maybe<kind>
  fun kgammaFind(ctxt: name, name: name): (name, kind)
  fun kgammaList(): list<(name, list<(name, kind)>)>
  fun kgammaFilter(modName: name): qname-map<kind>
  fun kgammaUnions(ks: list<qname-map<kind>>): qname-map<kind>

fun withKGamma(kg0: qname-map<kind>, f: () -> <kGamma,exn,compFlags|e> a): <exn,compFlags|e> a
  var kg := kg0
  with handler
    fun kgammaExtend(name: name, k: kind)
      kg := kg.insert(name, k)
    fun kgammaLookup(ctxt, name: name)
      kg.lookup(ctxt, name)
    fun kgammaLookupQ(name: name)
      kg.lookupQ(name)
    fun kgammaFind(ctxt: name, name: name)
      match kg.lookup(ctxt, name)
        Found((qn, scheme)) -> (qn, scheme)
        _ -> fail("kind lookup failed")
    fun kgammaList()
      kg.list
    fun kgammaFilter(modName: name)
      kg.filterNames(fn(n) n == modName)
    fun kgammaUnions(ks: list<qname-map<kind>>)
      kg := unions(ks)
      kg
  f()

val eqK = fn(k1:kind, k2:kind) k1 == k2
val showK = fn(k:kind) k.show
fun single(name: name, k: kind): qname-map<kind>
  name-collections/single(name, k, eqK, showK)

val empty = name-collections/qname-empty(eqK, showK)

fun extractKGamma(c: core): <exn,compFlags> qname-map<kind>
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <exn,compFlags> qname-map<kind>
  g.map(extractTypeDef).unions

fun extractTypeDef(d: typeDef): qname-map<kind>
  match d
    Synonym(synInfo) | synInfo.vis.is-public -> single(synInfo.name, synInfo.kind)
    Data(dataInfo, False) | dataInfo.vis.is-public -> single(dataInfo.name, dataInfo.kind)
    _ -> empty

// TODO: Pretty print
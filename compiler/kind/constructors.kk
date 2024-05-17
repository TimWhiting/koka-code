import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap

effect constructors
  fun constructorsExtend(name: name, c: conInfo): ()
  fun constructorsLookup(ctxt: name, name: name): lookup<conInfo>
  fun constructorsLookupQ(name: name): maybe<conInfo>
  fun constructorsFind(ctxt: name, name: name): (name, conInfo)
  fun constructorsList(): list<(name, list<(name, conInfo)>)>
  fun constructorsFilter(modName: name): qname-map<conInfo>
  fun constructorsUnions(cs: list<qname-map<conInfo>>): qname-map<conInfo>

fun withConstructors(cnstrs0: qname-map<conInfo>, f: () -> <constructors,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var cnstrs := cnstrs0
  with handler
    fun constructorsExtend(name: name, k: conInfo)
      cnstrs := cnstrs.insert(name, k)
    fun constructorsLookup(ctxt, name: name)
      cnstrs.lookup(ctxt, name)
    fun constructorsLookupQ(name: name)
      cnstrs.lookupQ(name)
    fun constructorsFind(ctxt: name, name: name)
      match cnstrs.lookup(ctxt, name)
        Found((qn, conInfo)) -> (qn, conInfo)
        _ -> fail("conInfo lookup failed")
    fun constructorsList()
      cnstrs.list
    fun constructorsFilter(modName: name)
      cnstrs.filterNames(fn(n) n == modName)
    fun constructorsUnions(cs: list<qname-map<conInfo>>)
      cnstrs := unions(cs.reverse) // Assumes left bias
      cnstrs
  f()

val eqC = fn(c1:conInfo, c2:conInfo) c1 == c2
val showC = fn(c:conInfo) c.show
fun single(name: name, c: conInfo): qname-map<conInfo>
  name-collections/single(name, c, eqC, showC)

val empty = name-collections/qname-empty(eqC, showC)

fun extractConstructors(c: core): <pure,comp-flags> qname-map<conInfo>
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <pure,comp-flags> qname-map<conInfo>
  g.map(extractTypeDef).unions

fun extractTypeDef(d: typeDef): <pure,comp-flags> qname-map<conInfo>
  match d
    Data(dataInfo) | dataInfo.vis.is-public -> 
      fromList(dataInfo.constrs.filter(fn(ci) ci.vis.is-public).map(fn(ci) (ci.name, ci)), eqC, showC)
    _ -> empty

// TODO: Pretty print
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
  fun constructorsLookup(name: name): maybe<conInfo>
  fun constructorsFind(name: name): conInfo
  fun constructorsList(): list<(name, conInfo)>
  fun constructorsFindScheme(name: name): ktype
  fun constructorsUnions(cs: list<name-map<conInfo>>): name-map<conInfo>

fun withConstructors(cnstrs0: name-map<conInfo>, f: () -> <constructors,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var cnstrs := cnstrs0
  with handler
    fun constructorsExtend(name: name, k: conInfo)
      cnstrs := cnstrs.set(name, k)
    fun constructorsLookup(name: name)
      cnstrs.lookup(name)
    fun constructorsFind(name: name)
      match cnstrs.lookup(name)
        Just(conInfo) -> conInfo
        _ -> fail("conInfo lookup failed")
    fun constructorsList()
      cnstrs.list
    fun constructorsFindScheme(name: name)
      cnstrs.map/get(name).typeScheme
    fun constructorsUnions(cs: list<name-map<conInfo>>)
      cnstrs := unions(cs.reverse) // Assumes left bias
      cnstrs
  f()

val contructors/empty: name-map<conInfo> = LinearMap([])

fun compose(a: name-map<conInfo>, b: name-map<conInfo>): name-map<conInfo>
  a.union(b) // ASSUMES left biased union

fun core/extract-coninfo(c: core): <pure,comp-flags> name-map<conInfo>
  c.typeDefs.map(extract-coninfo).unions

fun tdg/extract-coninfo(g: typeDefGroup): <pure,comp-flags> name-map<conInfo>
  g.map(extract-coninfo).unions

fun td/extract-coninfo(d: typeDef): <pure,comp-flags> name-map<conInfo>
  match d
    Data(dataInfo) | dataInfo.vis.is-public -> 
      LinearMap(dataInfo.constrs.filter(fn(ci) ci.vis.is-public).list/map(fn(ci) (ci.conInfo/name, ci)))
    _ -> empty

// TODO: Pretty print
import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearmap

alias newtypes = name-map<dataInfo>

effect newtypesEff
  fun newtypesExtend(name: name, newtp: dataInfo): ()
  fun newtypesLookupAny(name: name): maybe<dataInfo>
  fun newtypesLookupPublic(name: name): maybe<dataInfo>
  fun newtypesFind(name: name): dataInfo
  fun newtypesList(): list<(name, dataInfo)>

fun withNewtypes(newtps0: newtypes, f: () -> <newtypesEff,exn,compFlags|e> a): <exn,compFlags|e> a
  var newtps := newtps0
  with handler
    fun newtypesExtend(name: name, k: dataInfo) newtps := newtps.set(name, k)
    fun newtypesLookupAny(name: name) newtps.maybeGet(name)
    fun newtypesLookupPublic(name: name) newtps.newtypesLookupPublic(name)
    fun newtypesFind(name: name) newtps.newtypesFind(name)
    fun newtypesList() newtps.list
  f()

fun newtypesNew(lst: list<dataInfo>): newtypes
  linearMap(lst.map(fn(di) (di.name, di)), (==), eqD, show, showD)
fun newtypesExtend(newtps: newtypes, name: name, k: dataInfo)
  newtps.set(name, k)
fun newtypesLookupAny(newtps: newtypes, name: name)
  newtps.maybeGet(name)
fun newtypesLookupPublic(newtps: newtypes, name: name)
  match newtps.maybeGet(name)
    Just(di) | di.vis.is-public -> Just(di)
    _ -> Nothing
fun newtypesFind(newtps: newtypes, name: name)
  match newtps.maybeGet(name)
    Just(di) -> di
    _ -> fail("newTypes lookup failed")
fun newtypesCompose(ntps1: newtypes, ntps2: newtypes)
  unions([ntps2, ntps1])

val eqD = fn(d1:dataInfo, d2:dataInfo) d1 == d2
val showD = fn(d:dataInfo) d.show
fun single(name: name, d: dataInfo): newtypes
  linearMap([(name, d)], (==), eqD, show, showD)
val emptyNewtypes:newtypes = linearMap([], fn(n1: name, n2: name) n1 == n2, eqD, show, showD)

fun extractNewtypes(c: core): <pure,compFlags> newtypes
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <pure,compFlags> newtypes
  g.map(extractTypeDef).unions

fun extractTypeDef(d: typeDef): <pure,compFlags> newtypes
  match d
    Data(dataInfo, False) -> single(dataInfo.name, dataInfo)
    _ -> emptyNewtypes

// TODO: Pretty print
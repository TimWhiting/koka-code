import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearmap

effect newtypes
  fun newtypesExtend(name: name, newtp: dataInfo): ()
  fun newtypesLookupAny(name: name): maybe<dataInfo>
  fun newtypesLookupPublic(name: name): maybe<dataInfo>
  fun newtypesFind(name: name): dataInfo
  fun newtypesList(): list<(name, dataInfo)>
  fun newtypesCompose(ntps1: name-map<dataInfo>, ntps2: name-map<dataInfo>): name-map<dataInfo>

fun withNewtypes(newtps0: name-map<dataInfo>, f: () -> <newtypes,exn,compFlags|e> a): <exn,compFlags|e> a
  var newtps := newtps0
  with handler
    fun newtypesExtend(name: name, k: dataInfo)
      newtps := newtps.set(name, k)
    fun newtypesLookupAny(name: name)
      newtps.maybeGet(name)
    fun newtypesLookupPublic(name: name)
      match newtps.maybeGet(name)
        Just(di) | di.vis.is-public -> Just(di)
        _ -> Nothing
    fun newtypesFind(name: name)
      match newtps.maybeGet(name)
        Just(di) -> di
        _ -> fail("newTypes lookup failed")
    fun newtypesList()
      newtps.list
    fun newtypesCompose(ntps1: name-map<dataInfo>, ntps2: name-map<dataInfo>)
      newtps := unions([ntps2, ntps1])
      newtps
  f()

val eqD = fn(d1:dataInfo, d2:dataInfo) d1 == d2
val showD = fn(d:dataInfo) d.show
fun single(name: name, d: dataInfo): name-map<dataInfo>
  linearMap([(name, d)], (==), eqD, show, showD)
val empty:name-map<dataInfo> = linearMap([], fn(n1: name, n2: name) n1 == n2, eqD, show, showD)

fun extractNewtypes(c: core): <pure,compFlags> name-map<dataInfo>
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <pure,compFlags> name-map<dataInfo>
  g.map(extractTypeDef).unions

fun extractTypeDef(d: typeDef): <pure,compFlags> name-map<dataInfo>
  match d
    Data(dataInfo, False) -> single(dataInfo.name, dataInfo)
    _ -> empty

// TODO: Pretty print
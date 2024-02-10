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

fun withNewtypes(newtps0: newtypes, f: () -> <newtypesEff,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var newtps := newtps0
  with handler
    fun newtypesExtend(name: name, k: dataInfo) newtps := newtps.set(name, k)
    fun newtypesLookupAny(name: name) newtps.maybe-get(name)
    fun newtypesLookupPublic(name: name) newtps.newtypesLookupPublic(name)
    fun newtypesFind(name: name) newtps.newtypesFind(name)
    fun newtypesList() newtps
  f()

fun nt/newtypesNew(lst: list<dataInfo>): newtypes
  lst.map(fn(di) (di.name, di))
fun nt/newtypesExtend(newtps: newtypes, name: name, k: dataInfo)
  newtps.set(name, k)
fun nt/newtypesLookupAny(newtps: newtypes, name: name)
  newtps.maybe-get(name)
fun nt/newtypesLookupPublic(newtps: newtypes, name: name)
  match newtps.maybe-get(name)
    Just(di) | di.vis.is-public -> Just(di)
    _ -> Nothing
fun nt/newtypesFind(newtps: newtypes, name: name)
  match newtps.maybe-get(name)
    Just(di) -> di
    _ -> fail("newTypes lookup failed")
fun newtypesCompose(ntps1: newtypes, ntps2: newtypes)
  unions([ntps2, ntps1])

fun single(name: name, d: dataInfo): newtypes
  [(name, d)]
val emptyNewtypes:newtypes = []

fun extractNewtypes(c: core): <pure,comp-flags> newtypes
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <pure,comp-flags> newtypes
  g.map(extractTypeDef).unions

fun extractTypeDef(d: typeDef): <pure,comp-flags> newtypes
  match d
    Data(dataInfo, False) -> single(dataInfo.name, dataInfo)
    _ -> emptyNewtypes

// TODO: Pretty print
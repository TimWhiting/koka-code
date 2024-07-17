import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap

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
    fun newtypesLookupAny(name: name) newtps.lookup-any(name)
    fun newtypesLookupPublic(name: name) newtps.lookup-public(name)
    fun newtypesFind(name: name) newtps.newtypes/find(name)
    fun newtypesList() newtps.list
  f()

fun newtypes/new(lst: list<dataInfo>): newtypes
  LinearMap(lst.map(fn(di) (di.name, di)))
fun newtypes/extend(newtps: newtypes, name: name, k: dataInfo)
  newtps.set(name, k)
fun newtypes/lookup-any(newtps: newtypes, name: name)
  newtps.lookup(name)
fun newtypes/lookup-public(newtps: newtypes, name: name)
  match newtps.lookup(name)
    Just(di) | di.vis.is-public -> Just(di)
    _ -> Nothing
fun newtypes/find(newtps: newtypes, name: name)
  match newtps.lookup(name)
    Just(di) -> di
    _ -> fail("newTypes lookup failed")
fun newtypesCompose(ntps1: newtypes, ntps2: newtypes)
  unions([ntps2, ntps1])

fun single(name: name, d: dataInfo): newtypes
  LinearMap([(name, d)])
val newtypes/empty:newtypes = LinearMap([])

fun core/extract-newtypes(c: core): <pure,comp-flags> newtypes
  c.typeDefs.map(extract-newtypes).unions

fun tdg/extract-newtypes(g: typeDefGroup): <pure,comp-flags> newtypes
  g.map(extract-newtypes).unions

fun td/extract-newtypes(d: typeDef): <pure,comp-flags> newtypes
  match d
    Data(dataInfo, False) -> single(dataInfo.name, dataInfo)
    _ -> newtypes/empty

// TODO: Pretty print
import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap

alias synonyms = name-map<synInfo>
effect synonymsEff
  fun synonymsExtend(newtp: synInfo): ()
  fun synonymsLookup(name: name): maybe<synInfo>
  fun synonymsFind(name: name): synInfo
  fun synonymsList(): list<(name, synInfo)>
  fun synonymsFilter(modName: name): synonyms
  fun getSynonyms(): synonyms
  fun setSynonyms(syns: synonyms): ()

fun withSynonyms(synonyms0: synonyms, f: () -> <synonymsEff,pure,comp-flags|e> a): <pure,comp-flags|e> a
  var synonyms := synonyms0
  with handler
    fun getSynonyms() synonyms
    fun setSynonyms(syns: synonyms) synonyms := syns
    fun synonymsExtend(k: synInfo)
      synonyms := synonyms.extend(k)
    fun synonymsLookup(name: name)
      synonyms.lookup(name)
    fun synonymsFind(name: name)
      synonyms.synonyms/find(name)
    fun synonymsList()
      synonyms.list
    fun synonymsFilter(modName: name)
      synonyms.filter(fn(k, v) (k.qualifier) == modName)
      // TODO: Should this modify the synonyms?
  f()

fun new(ls: list<synInfo>)
  LinearMap(ls.map(fn(si) (si.name, si)))
fun extend(synonyms: synonyms, k: synInfo)
  synonyms.set(k.name, k)
fun lookup(synonyms: synonyms, name: name)
  synonyms.lookup(name)
fun find(synonyms: synonyms, name: name)
  match synonyms.lookup(name)
    Just(di) -> di
    _ -> fail("synonyms lookup failed")
fun diff(synonyms: synonyms, syns1: synonyms, syns2: synonyms)
  syns2.filter(fn(k, v) syns1.lookup(k).is-nothing)
fun synonyms/filter(synonyms: synonyms, modName: name)
  synonyms.filter(fn(k, v) (k.qualifier) == modName)

fun compose(syns1: synonyms, syns2: synonyms)
  unions([syns2, syns1])

fun single(name: name, s: synInfo): synonyms
  LinearMap([(name, s)])
val empty:synonyms = LinearMap([])

fun core/extract-synonyms(c: core): <pure,comp-flags> synonyms
  c.typeDefs.map(extract-synonyms).unions

fun tdg/extract-synonyms(g: typeDefGroup): <pure,comp-flags> synonyms
  g.map(extract-synonyms).unions

fun td/extract-synonyms(d: typeDef): <pure,comp-flags> synonyms
  match d
    Synonym(synInfo) -> single(synInfo.name, synInfo)
    _ -> empty

// TODO: Pretty print
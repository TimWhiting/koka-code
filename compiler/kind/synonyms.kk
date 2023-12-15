import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearmap

alias synonyms = name-map<synInfo>
effect synonymsEff
  fun synonymsExtend(newtp: synInfo): ()
  fun synonymsLookup(name: name): maybe<synInfo>
  fun synonymsFind(name: name): synInfo
  fun synonymsList(): list<(name, synInfo)>
  fun synonymsFilter(modName: name): synonyms
  fun getSynonyms(): synonyms
  fun setSynonyms(syns: synonyms): ()

fun withSynonyms(synonyms0: synonyms, f: () -> <synonymsEff,exn,compFlags|e> a): <exn,compFlags|e> a
  var synonyms := synonyms0
  with handler
    fun getSynonyms() synonyms
    fun setSynonyms(syns: synonyms) synonyms := syns
    fun synonymsExtend(k: synInfo)
      synonyms := synonyms.synonymsExtend(k)
    fun synonymsLookup(name: name)
      synonyms.maybeGet(name)
    fun synonymsFind(name: name)
      synonyms.synonymsFind(name)
    fun synonymsList()
      synonyms.list
    fun synonymsFilter(modName: name)
      synonyms.filter(fn(k, v) (k.qualifier) == modName)
      // TODO: Should this modify the synonyms?
  f()

fun synonymsNew(ls: list<synInfo>)
  linearMap(ls.map(fn(si) (si.name, si)))
fun synonymsExtend(synonyms: synonyms, k: synInfo)
  synonyms.set(k.name, k)
fun synonymsLookup(synonyms: synonyms, name: name)
  synonyms.maybeGet(name)
fun synonymsFind(synonyms: synonyms, name: name)
  match synonyms.maybeGet(name)
    Just(di) -> di
    _ -> fail("synonyms lookup failed")
fun synonymsDiff(synonyms: synonyms, syns1: synonyms, syns2: synonyms)
  syns2.filter(fn(k, v) syns1.maybeGet(k).is-nothing)
fun synonymsFilter(synonyms: synonyms, modName: name)
  synonyms.filter(fn(k, v) (k.qualifier) == modName)

fun synonymsCompose(syns1: synonyms, syns2: synonyms)
  unions([syns2, syns1])

fun single(name: name, s: synInfo): synonyms
  linearMap([(name, s)])
val emptySynonyms:synonyms = linearMap([])

fun extractSynonyms(c: core): <pure,compFlags> synonyms
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <pure,compFlags> synonyms
  g.map(extractSynonyms).unions

fun extractSynonyms(d: typeDef): <pure,compFlags> synonyms
  match d
    Synonym(synInfo) -> single(synInfo.name, synInfo)
    _ -> emptySynonyms

// TODO: Pretty print
import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearmap

effect synonyms
  fun synonymsExtend(newtp: synInfo): ()
  fun synonymsLookup(name: name): maybe<synInfo>
  fun synonymsFind(name: name): synInfo
  fun synonymsList(): list<(name, synInfo)>
  fun synonymsCompose(syns1: name-map<synInfo>, syns2: name-map<synInfo>): name-map<synInfo>
  fun synonymsDiff(syns1: name-map<synInfo>, syns2: name-map<synInfo>): name-map<synInfo>
  fun synonymsFilter(modName: name): name-map<synInfo>
  fun getSynonyms(): name-map<synInfo>
  fun setSynonyms(syns: name-map<synInfo>): ()

fun withSynonyms(synonyms0: name-map<synInfo>, f: () -> <synonyms,exn,compFlags|e> a): <exn,compFlags|e> a
  var synonyms := synonyms0
  with handler
    fun getSynonyms()
      synonyms
    fun setSynonyms(syns: name-map<synInfo>)
      synonyms := syns
    fun synonymsExtend(k: synInfo)
      synonyms := synonyms.set(k.name, k)
    fun synonymsLookup(name: name)
      synonyms.maybeGet(name)
    fun synonymsFind(name: name)
      match synonyms.maybeGet(name)
        Just(di) -> di
        _ -> fail("synonyms lookup failed")
    fun synonymsList()
      synonyms.list
    fun synonymsCompose(syns1: name-map<synInfo>, syns2: name-map<synInfo>)
      synonyms := unions([syns2, syns1])
      synonyms
    fun synonymsDiff(syns1: name-map<synInfo>, syns2: name-map<synInfo>)
      syns2.filter(fn(k, v) syns1.maybeGet(k).is-nothing)
      // TODO: Should this modify the synonyms?
    fun synonymsFilter(modName: name)
      synonyms.filter(fn(k, v) (k.qualifier) == modName)
      // TODO: Should this modify the synonyms?
  f()

val eqS = fn(s1:synInfo, s2:synInfo) s1 == s2
val showS = fn(s:synInfo) s.show
fun single(name: name, s: synInfo): name-map<synInfo>
  linearMap([(name, s)], (==), eqS, show, showS)
val emptySynonyms:name-map<synInfo> = linearMap([], fn(n1: name, n2: name) n1 == n2, eqS, show, showS)

fun extractSynonyms(c: core): <pure,compFlags> name-map<synInfo>
  c.typeDefs.map(extractTypeDefGroup).unions

fun extractTypeDefGroup(g: typeDefGroup): <pure,compFlags> name-map<synInfo>
  g.map(extractSynonyms).unions

fun extractSynonyms(d: typeDef): <pure,compFlags> name-map<synInfo>
  match d
    Synonym(synInfo) -> single(synInfo.name, synInfo)
    _ -> emptySynonyms

// TODO: Pretty print
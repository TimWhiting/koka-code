import compiler/common/range
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/common/name
import compiler/common/name-collections
import compiler/common/failure
import compiler/platform/config
import compiler/lib/pprint
import compiler/kind/kind
import compiler/kind/infer-kind
import compiler/kind/assumption
import compiler/kind/synonyms
import compiler/kind/newtypes
import compiler/kind/importmap
import compiler/type/type
import compiler/syntax/range-map
import compiler/syntax/syntax
import compiler/core/core
import newstd/data/linearmap

struct inferKindEnv
  currentModule: name
  imports: importmap
  kGamma: kGamma
  infgamma: infKGamma
  synonyms: synonyms
  newtypesImported: newtypes
  newtypesExtended: newtypes

fun allnewtypes(infKindEnv: inferKindEnv)
  infKindEnv.newtypesImported.newtypesCompose(infKindEnv.newtypesExtended)

fun runKindInfer(platform: platform, mbRangeMap: maybe<range-map>, moduleName: name, imports: importmap, kgamma: kGamma, syns: synonyms, datas: newtypes, f: () -> <inferKindEff,pure,colorSchemeEffect,uniquePhase> a): <pure,colorSchemeEffect,uniquePhase> (list<(doc,range)>, list<(doc,range)>, maybe<range-map>, a)
  val imports' = match imports.importsExtend(moduleName, moduleName)
    Just(imp) -> imp
    Nothing -> imports // ignore
  with handler
    val infKindEnv = InferKindEnv(moduleName, imports', kgamma, infKGammaEmpty, syns, datas, emptyNewtypes)
  var errs := []
  var warns := []
  var rm := mbRangeMap
  var ksub := ksubEmpty
  with handler
    fun addWarning(d, rng) warns := Cons((d, rng), warns)
    fun addError(d, rng) errs := Cons((d, rng), errs)
    fun getKsub() ksub
    fun extendKsub(s) ksub := ksub.compose(s)
    fun addRangeInfo(r, info) rm := rm.map(fn(rm') rm'.insert(r, info))
    val platform = platform
  (errs, warns, rm, f())

alias inferKindEff = <inferKindEnvEffect, inferKindEffect>

effect inferKindEnvEffect
  val infKindEnv: inferKindEnv

effect inferKindEffect
  fun addError(d: doc, r: range): ()
  fun addWarning(d: doc, r: range): ()
  fun getKsub(): ksub
  fun extendKsub(s: ksub): ()
  fun addRangeInfo(r: range, info: rangeInfo): ()
  val platform: platform

fun freshKind()
  KIVar(uniqueId("k"))

fun freshTypeVar(TypeBinder(name, kind): typeBinder<kind>, fl: flavour)
  TypeVar(uniqueId(name.show), kind, fl)

fun subst(x: infKind)
  getKsub() |-> x

// Extend the inference kind assumption; checks for 'shadow' definitions
fun extendInfGamma(tbinders: list<typeBinder<infKind>>, f)
  fun check(TypeBinder(nm, infkind, nmrng, _): typeBinder<infKind>, infgamma: infKGamma)
    match infgamma.maybeGet(nm)
      Nothing -> infgamma.add(nm, infkind)
      Just(_) ->
        addError("Type".text |+| nm.ppType |+| "is already defined".text, nmrng)
        infgamma.set(nm, infkind) // replace
  val infgammaNew = tbinders.foldl(infKindEnv.infgamma, fn(acc, tb) tb.check(acc))
  with override
    val infKindEnv = infKindEnv( infgamma = infgammaNew)
  f()

// Extend the kind assumption; checks for duplicate definitions
fun extendKGamma(rngs: list<range>, dg: compiler/core/core/typeDefGroup, f)
  fun nameKind(tdef: compiler/core/core/typeDef)
    match tdef
      core/Synonym(synInfo) -> (synInfo.name, synInfo.kind)
      core/Data(ntInfo) -> (ntInfo.name, ntInfo.kind)
  fun check((kgamma: kGamma, tdefs: list<compiler/core/core/typeDef>), (rng: range, tdef: compiler/core/core/typeDef))
    if tdef.isExtension then (kgamma, tdefs)
    else
      val (nm, knd) = nameKind(tdef)
      match kgamma.kgammaLookupQ(nm)
        Nothing -> (kgamma.kgammaExtend(nm, knd), Cons(tdef, tdefs))
        Just(_) ->
          addError("Type".text |+| nm.ppType |+| "is already defined".text, rng)
          (kgamma, tdefs)
  val (_, tdefs) = zip(rngs, dg).foldl((infKindEnv.kGamma, []), check)
  
  fun nameSyn(tdef: compiler/core/core/typeDef)
    match tdef
      core/Synonym(synInfo) -> [synInfo]
      _ -> []
  fun nameNewtype(tdef: compiler/core/core/typeDef)
    match tdef
      Data(dataInfo) -> [dataInfo]
      _ -> []
  val newkGamma = kgammaNewNub(tdefs.map(nameKind))
  val kSyns = synonymsNew(tdefs.map(nameSyn).concat)
  val kNewtypes = newtypesNew(tdefs.map(nameNewtype).concat)
  with override
    val infKindEnv = infKindEnv( 
      kGamma = infKindEnv.kGamma.union(newkGamma), 
      synonyms = infKindEnv.synonyms.synonymsCompose(kSyns), 
      newtypesExtended = infKindEnv.newtypesExtended.newtypesCompose(kNewtypes))  
  f()

fun infQualifiedName(nm: name, rng: range)
  if !nm.isQualified then nm
  else
    match importsExpand(infKindEnv.imports, nm)
      Right((name', alias0)) ->
        if !nm.qualifier.nameCaseEqual(alias0) then
          addError("module".text |+| nm.ppModule |+| "should be cased as".text |+| alias0.pretty.color(colors.colorModule), rng)
          name'
        else
          name'
      Left([]) ->
        addError("module".text |+| nm.pretty.color(colors.colorModule) |+| "is undefined".text, rng)
        nm
      Left(aliases) ->
        addError("module".text |+| nm.pretty.color(colors.colorModule) |+| ambiguous(aliases), rng)
        nm

fun ppModule(nm: name)
  nm.nameModule.text.color(colors.colorModule)

fun findInfKind(nm0: name, rng: range)
  val (nm, mbAlias) = match importsExpand(infKindEnv.imports, nm0)
    Right((name', alias0)) -> (name', Just(alias0))
    _ -> (nm0, Nothing)
  val qname = if nm.isQualified then nm else qualify(infKindEnv.currentModule, nm)
  // lookup locally
  // note: also lookup qualified since it might be recursive definition
  // TODO: check for the locally inferred names for casing too.
  val infgamma = infKindEnv.infgamma
  match infgamma.maybeGet(nm)
    Just(infkind) -> (nm, infkind)
    Nothing ->
      match infgamma.maybeGet(qname)
        Just(infkind) -> (qname, infkind)
        _ ->
          val kgamma = infKindEnv.kGamma  
          match kgamma.kgammaLookup(infKindEnv.currentModule, nm)
            Found((qname', kind)) ->
              val name' = if nm.isQualified then qname' else qname'.unqualify
              if !name'.nameCaseEqual(nm) then
                addError("type".text |+| nm0.unqualify.ppType |+| "should be cased as".text |+| name'.unqualify.ppType, rng)
              else
                ()
              match mbAlias
                Just(alias0) | nm0.nameModule != alias0.showPlain ->
                  addError("module".text |+| nm0.nameModule.text.color(colors.colorModule) |+| "should be cased as ".text |+| alias0.pretty.color(colors.colorModule), rng)
                _ -> ()
              (qname, KICon(kind))
            NotFound ->
              addError("Type".text |+| nm.ppType |+| "is not defined".text |-| " hint: bind the variable using".text |+| ("forall<".text |.| nm.ppType |.| ">".text).color(colors.colorType) |+| "?".text, rng)
              val k = freshKind()
              (nm, k)
            Ambiguous(names) ->
              addError("Type".text |+| nm.ppType |+| ambiguous(names), rng)
              val k = freshKind()
              (nm, k)

fun ambiguous(lst: list<name>)
  match lst
    [name1, name2] -> "is ambiguous.".text |-| " hint: It can refer to either".text |+| name1.ppType |.| ", or".text |+| name2.ppType
    [name1, name2, name3] -> "is ambiguous.".text |-| " hint: It can refer to either".text |+| name1.ppType |.| ", ".text |+| name2.ppType |.| ", or".text |+| name3.ppType
    [name] -> "should be cased as:".text |+| name.unqualify.ppType
    names -> "is ambiguous and can refer to multiple imports:".text |-| names.map(ppType).list.indent(1)

fun ppType(nm: name)
  nm.pretty.color(colors.colorType)

fun qualifyDef(nm: name)
  qualify(infKindEnv.currentModule, nm)

fun findKind(nm: name)
  match kgammaLookup(infKindEnv.currentModule, nm)
    Found((qname, kind)) -> (qname, kind)
    _ -> fail("kind/infer findKind: unknown type constructor: " ++ nm.show)

fun lookupDataInfo(nm: name)
  match infKindEnv.newtypesExtended.newtypesLookupAny(nm)
    Nothing -> infKindEnv.newtypesImported.newtypesLookupPublic(nm)
    just -> just
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
  infgamma: infKGamma
  newtypesImported: newtypes
  newtypesExtended: newtypes
  currentModule: name

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


// TODO:





fun ppModule(nm: name)
  nm.nameModule.text.color(colors.colorModule)

// TODO;

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
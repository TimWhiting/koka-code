import compiler/common/id
import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/printer
import compiler/type/type
import compiler/common/name
import newstd/data/linearmap
import compiler/kind/importmap
import compiler/platform/config
import compiler/common/nice
import compiler/kind/kind

alias prec = int;
val precTopTop = -1 // most outer level: used to suppress 'forall'
val precTop = 0
val precQuant = 1
val precArrow = 2
val precApp = 3
val precAtom = 4
val precPred = 5

alias tvScheme = linearMap<typeVar, (prec -> doc)>;

val rankedDefault = linearMap([], fn(t1: typeVar, t2: typeVar) t1 == t2, fn(_, _) True, show, fn(_) "")

// Find a better place for this
// Contains link bases for documentation generation (see Syntax.Colorize)
effect documentation
  val colorizing: bool
  val htmlBases: list<(string, string)>
  val htmlCss: string
  val htmlJs: string

// find a better place for this
// Signifies whether we output core for an interface or not
effect coreOptions
  val coreIface: bool
  val coreShowTypes: bool // show types in core output
  val coreShowVis: bool // show visibility
  val coreShowDef: bool; // show definition body

fun defaultDocEnv(f)
  with handler
    val colorizing = False
    val htmlBases = []
    val htmlCss = "styles/" ++ compFlags.programName ++ ".css"
    val htmlJs = "scripts/" ++ compFlags.programName ++ "-highlight.js"
  f()

fun defaultCoreOptions(f)
  with handler
    val coreIface = False
    val coreShowTypes = False
    val coreShowVis = True
    val coreShowDef = False
  f()

// Pretty print environment for types

effect prettyTypeEff
  val showKinds: bool
  val showIds: bool // show id numbers
  val expandSynonyms: bool
  val colors: colorScheme
  val prec: prec
  val ranked: tvScheme
  val moduleContext: name // module in which we pretty print
  val importsMap: importmap // import aliases
  val fullNames: bool

fun ".default-prettyTypeEff"(f)
  handle(f)
    val showKinds = False
    val showIds = False
    val expandSynonyms = False
    val colors = ColorScheme()
    val prec = precTopTop
    val ranked = rankedDefault
    val moduleContext = "Main".newName
    val importsMap = emptyImports
    val fullNames = False
 
fun typeColor(colors: colorScheme)
  ":".text.color(colors.colorSep)

fun minCanonical(tp: ktype): pure string
  tp.minimalForm.show.compress

fun canonical(tp: ktype): pure string
  tp.canonicalForm.show.compress

fun compress(s: string): string
  s.list.compress.string

fun compress(l: list<char>): list<char>
  match l
    Nil -> Nil
    Cons(c, cs) ->
      if c == '\n' then compress(cs.drop-while(isSpace).unsafe-decreasing)
      elif c.isSpace then  Cons(' ', compress(cs.drop-while(isSpace).unsafe-decreasing))
      else Cons(c, compress(cs))

// fun niceType(tp)
//   niceTypes([tp]).head.unjust

// fun niceTypes(tps: list<ktype>): list<doc>
//   tps.niceList fn(tp)
//     tp.ppType.color(prettyTypeEnv.colors.colorType)

// fun niceList(schemes: list<ktype>, f: (ktype) -> doc): list<doc>

fun ppTypeSyn(ts: typeSyn)
  ts.name.ppNameEx(ts.kind).wrapKind.colorByKindDef(kind, colorTypeCon)

fun colorByKindDef(d: doc, k: kind, defcolor: (colorScheme -> prettyTypeEff color))
  d.colorByKind(k, fn(d') d'.color(defcolor(colors)))

fun colorByKind(d: doc, k: kind, defcolor: (doc -> prettyTypeEff doc))
  match k.colorForKind
    Just(c) -> d.color(c)
    Nothing -> defcolor(d)

fun colorForKind(k: kind)
  if k == kindEffect || k == kindLabel || k == kindFun(kindHeap, kindLabel) then
    Just(colors.colorEffect)
  elif k == kindHeap || k == kindScope then
    Just(colors.colorEffect)
  else Nothing

fun wrapKind(d: doc, k: kind)
  if showKinds && k != kindStar then
    parens(d.color(colors.colorType) |+| "::".text |+| k.ppKind(precTop)).color(colors.colorKind)
  else d
import compiler/common/id
import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/type/type
import compiler/common/name
import newstd/data/linearmap
import compiler/kind/importmap
import compiler/platform/config

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
struct prettyTypeEnv
  showKinds: bool = False
  showIds: bool = False // show id numbers
  expandSynonyms: bool = False
  colors: colorScheme = ColorScheme()
  nice: nice = niceEmpty
  prec: prec = precTopTop
  ranked: tvScheme = rankedDefault
  moduleContext: name = "Main".newName // module in which we pretty print
  importsMap: importmap = emptyImports // import aliases
  fullNames: bool = False;

effect prettyTypeEff
  val prettyTypeEnv: prettyTypeEnv

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
  
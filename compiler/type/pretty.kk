import compiler/common/id
import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/printer
import compiler/type/type
import compiler/common/name
import compiler/common/name-prim
import newstd/data/linearmap
import compiler/kind/importmap
import compiler/platform/config
import compiler/common/nice
import compiler/type/kind
import compiler/kind/kind
import compiler/kind/pretty
import compiler/common/syntax

alias prec = int;
val precTopTop = -1 // most outer level: used to suppress 'forall'
val precTypeTop = 0
val precTypeQuant = 1
val precTypeArrow = 2
val precTypeApp = 3
val precTypeAtom = 4
val precPred = 5

alias tvScheme = linearMap<typeVar, (prec -> doc)>;

val rankedDefault = linearMap([], fn(t1: typeVar, t2: typeVar) t1 == t2, fn(_, _) True, show, fn(_) "")

fun keyword(s: string)
  s.text.color(colors.colorTypeKeyword)

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

alias ppTypeEff = <precEff,prettyTypeEff,documentation,coreOptions,pure>

effect precEff
  val prec: prec

effect prettyTypeEff
  val showKinds: bool
  val showIds: bool // show id numbers
  val expandSynonyms: bool
  val colors: colorScheme
  val ranked: tvScheme
  val moduleContext: name // module in which we pretty print
  val importsMap: importmap // import aliases
  val fullNames: bool

fun overridePrec(p: prec, f)
  with override 
    val prec = p
  f()

fun handlePrettyEff(f)
  with override
    val prec = precTopTop
  with handler 
    val showKinds = False
    val showIds = False
    val expandSynonyms = False
    val colors = ColorScheme()
    val ranked = rankedDefault
    val moduleContext = "Main".newName
    val importsMap = emptyImports
    val fullNames = False
  f()
 
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

fun niceType(tp)
  niceTypes([tp]).head.unjust

fun niceTypes(tps: list<ktype>): list<doc>
  tps.niceList fn(tp)
    tp.ppType.color(prettyTypeEnv.colors.colorType)

fun niceList(schemes: list<ktype>, f: (ktype) -> ppTypeEff doc): ppTypeEff list<doc>
  schemes.map(fn(tp) tp.typeVars).unions.list.map(extendNice)
  schemes.map(f)

// Pretty print a type
// ppScheme

// ppSchemeEffect

// ppDefFunType

// ppDeclType

fun commaSep(d: list<doc>)
  d.punctuate(comma).hsep


// prettyDataInfo

// prettyConInfo


fun prettyComment(d: doc, comment: string)
  if comment == "" then d else
    val clist = comment.list
    val cmt = if c.last.unjust == '\n' then c.init.string else comment
    (cmt.text |-| doc).color(colors.colorComment)

fun ppVis(v: visibility)
  match v
    Private -> empty
    Public -> "pub ".keyword

// Synonym info

// fun pretty(s: syninfo
//   with handlePrettyEff
//   ppSynInfo(s)

// fun ppSynInfo(s: synInfo, isLocal: bool=False, publicOnly:bool=False, showBody:bool=True)
  // if publicOnly && vis.isPrivate then empty else
  //   s.doc.prettyComment

fun ppType(tp: ktype)
  val t = match tp
    TForAll(vars, preds, t) ->
      val p = prec
      vars.map(fn(v) extendNice(v))
      val d = (if vars.is-nil then empty else "forall".keyword |.| vars.map(fn(v) v.ppTypeVar).angled |.| space)
      val d' = d |.| t.ppType |.| preds.ppPredicates
      d'.pparens(p, precTypeQuant)
    TFun(args, eff, res) -> ppFun("->".text, args, eff, res)
    TVar(tv as TypeVar(_, _, Bound)) ->
      match ranked.maybeGet(tv)
        Nothing -> tv.ppTypeVar
        Just(f) -> f(prec)
    TVar(tv) -> tv.ppTypeVar
    TCon(cv) -> ppTypeCon(cv)
    TApp(TCon(c), [_, _]) | c.name == nameEffectExtend ->
      val (ls, tl) = tp.shallowExtractEffectExtend
      val tldoc = if tl == effectEmpty then empty else "|".text |.| overridePrec(precTypeTop, {tl.ppType})
      val isCoreIface = coreIface
      val isTailEmpty = tl == effectEmpty 
      val doc = match ls
        [l] | isTailEmpty && !isCoreIface -> overridePrec(precTypeAtom, {l.ppType})
        _ -> "<".text |.| ls.map(fn(l) overridePrec(precTypeTop, {l.ppType})).punctuate(comma).hcat |.| tldoc |.| ">".text
      doc.color(colors.colorEffect)
    TApp(TCon(c), [eff, res]) | c.name == nameTpDelay ->
      "$".text |+| (if eff.isTypeTotal then empty else overridePrec(precArrow, {eff.ppType}) |.| space) |.|
      overridePrec(precArrow, {res.ppType})
    TApp(TCon(c), [arg]) ->
      if c.name == nameTpOptional && colorizing then
        "?".text |.| overridePrec(precTypeAtom, {arg.ppType})
      elif c.name == nameTpHandled || c.name == nameTpHandled1 && !coreIface then
        arg.ppType
      else
        match tp
          TApp(TCon(TypeCon(nm)), args) | nm.isNameTuple -> args.map(fn(t) overridePrec(precTypeTop, {t.ppType})).commaSep.parens
          TApp(f, args) ->
            val fdoc = overridePrec(precTypeAtom, {f.ppType})
            val argsdoc = match args 
              Nil -> empty
              Cons(arg, rest) -> 
                val argsDoc = args.map(fn(a) overridePrec(precTypeTop, {a.ppType})).angled
                if rest.is-nil then argsDoc.colorByKind(arg.kind, id) else argsDoc
            (fdoc |.| argsdoc).pparens(prec, precApp)
    // TODO: this is duplicated above due to issues with limitations in guards
    TApp(f, args) ->
      val fdoc = overridePrec(precTypeAtom, {f.ppType})
      val argsdoc = match args 
        Nil -> empty
        Cons(arg, rest) -> 
          val argsDoc = args.map(fn(a) overridePrec(precTypeTop, {a.ppType})).angled
          if rest.is-nil then argsDoc.colorByKind(arg.kind, id) else argsDoc
      (fdoc |.| argsdoc).pparens(prec, precApp)
    TSyn(syn, args, tp) ->
      overridePrec(precTop, {tp.ppType}).ppSynonym(syn, args)
  t.color(colors.colorType)

fun ppPredicates(preds: list<pred>)
  if preds.is-nil then empty
  else
    " with".keyword |+| preds.map(ppPred).hcat.align

fun ppFun(arrow, args, eff, result)
  args.map(fn(p) overridePrec(precTypeTop, {p.ppParam})).punctuate(comma).hsep.parens.pparens(prec, precTypeArrow) |+|
  (if eff.isTypeTotal then arrow else arrow |+| overridePrec(precTypeArrow, {eff.ppType})) |+|
  overridePrec(precTypeArrow, {result.ppType})

fun ppParam((nm: name, tp: ktype))
  val name = if !(nm.isNil || nm.isFieldName || nm.isWildcard) then
      nm.unqualify.ppNameEx.color(colors.colorParameter) |.| ":".text
    else
      empty
  name |.| tp.ppType

fun ppName(nm: name)
  nm.ppNameEx.color(colors.colorSource)

fun ppTypeName(nm: name)
  nm.ppNameEx.color(colors.colorType)

fun ppNameEx(n: name)
  if fullNames then n.pretty
  elif n.qualifier == moduleContext || n.isNameTuple || 
    ((n.qualifier == nameSystemCore || n.qualifier == nameCoreTypes) && !coreIface) then
    n.unqualify.pretty
  else
    importsMap.importsAlias(n).pretty

// Predicates
fun ppPred(pred: pred)
  val nm = match pred
    PredSub(tp1, tp2) ->
      overridePrec(precPred, {tp1.ppType}) |+| "<=".text |+| overridePrec(precPred, {tp2.ppType})
    PredIFace(nm, args) ->
      nm.ppTypeName |.| angled(args.map(fn(tp) overridePrec(precTypeTop, {tp.ppType})))
  nm.pparens(prec, precPred)

fun ppSynonym(tpdoc: doc, ts: typeSyn, args: list<ktype>)
  val nm = overridePrec(precTypeTop, {TApp(TCon(TypeCon(ts.name, ts.kind)), args).ppType}) |.| 
    (if expandSynonyms then " == ".text |.| ts.rank.pretty |+| tpdoc else empty)
  if expandSynonyms then
    nm.parens
  elif args.is-nil then
    nm
  else
    nm.pparens(prec, precTypeApp)

fun ppTypeVar(tv: typeVar)
  val fl = match tv.flavour
    Meta -> "_".text
    Skolem -> if coreIface then "__".text else "$".text
    _ -> empty
  val nm = fl |.| getNiceDoc(tv) |.| (if showIds then text("=" ++ tv.tid.show) else empty)
  nm.wrapKind(tv.kind).colorByKindDef(tv.kind, colorTypeVar)

fun ppTypeCon(tc: typeCon)
  tc.name.ppNameEx.wrapKind(tc.kind).colorByKindDef(tc.kind, colorTypeCon)

fun ppTypeSyn(ts: typeSyn)
  ts.name.ppNameEx.wrapKind(ts.kind).colorByKindDef(ts.kind, colorTypeCon)

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
    parens(d.color(colors.colorType) |+| "::".text |+| k.ppKind(colors, kind/pretty/precTop)).color(colors.colorKind)
  else d
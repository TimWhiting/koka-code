import compiler/common/id
import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/printer
import compiler/type/type
import compiler/type/typevar
import compiler/common/name
import compiler/common/name-prim
import std/data/linearmap
import std/data/linearset
import compiler/kind/importmap
import compiler/platform/config
import compiler/common/nice
import compiler/type/kind
import compiler/kind/kind
import compiler/kind/pretty
import compiler/common/syntax
import std/core/undiv

alias prec = int;
val precTopTop = -1 // most outer level: used to suppress 'forall'
val precTypeTop = 0
val precTypeQuant = 1
val precTypeArrow = 2
val precTypeApp = 3
val precTypeAtom = 4
val precPred = 5

alias tvScheme = linearMap<typeVar, (prec -> doc)>;

val rankedDefault:tvScheme = LinearMap([])

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

fun defaultDocEnv(f)
  with handler
    val colorizing = False
    val htmlBases = []
    val htmlCss = "styles/" ++ comp-flags.programName ++ ".css"
    val htmlJs = "scripts/" ++ comp-flags.programName ++ "-highlight.js"
  f()

fun defaultPPEnv(f)
  with handler
    val ppEnv = PpEnv()
  f()

// Pretty print environment for types

alias ppTypeEff = <ppTypeEnv,documentation,colorSchemeEffect,pure,niceEff<typeVar>,comp-flags>

effect precEff
  val prec: prec;

effect ppEnvEff
  val ppEnv: ppEnv;

struct ppEnv
  showKinds: bool = False
  showIds: bool = False // show id numbers
  expandSynonyms: bool = False
  fullNames: bool = False
  coreIface: bool = False
  coreShowTypes: bool = False // show types in core output
  coreShowVis: bool = True // show visibility
  coreShowDef: bool = False; // show definition body

alias ppTypeEnv = <prettyTypeEff,ppEnvEff,precEff>

effect prettyTypeEff
  val ranked: tvScheme
  val moduleContext: name // module in which we pretty print
  val importsMap: importmap // import aliases

fun overridePrec(p: prec, f)
  with override 
    val prec = p
  f()

fun handlePrettyEff(f)
  with handler
    val prec = precTopTop
  with handler 
    val ranked = rankedDefault
    val moduleContext = "Main".new-name
    val importsMap = LinearMap([])
  f()
 
fun typeColon()
  ":".text.color(colors.colorSep)

fun minCanonical(tp: ktype): pure string
  tp.minimalForm.show.compress

fun canonical(tp: ktype): pure string
  tp.canonicalForm.show.compress

fun string/compress(s: string): string
  s.list.compress.string

fun list/compress(l: list<char>): list<char>
  match l
    Nil -> Nil
    Cons(c, cs) ->
      if c == '\n' then compress(cs.drop-while(isSpace).pretend-decreasing)
      elif c.isSpace then  Cons(' ', compress(cs.drop-while(isSpace).pretend-decreasing))
      else Cons(c, compress(cs))

fun niceType(tp)
  niceTypes([tp]).head.unjust

fun niceTypes(tps: list<ktype>): ppTypeEff list<doc>
  tps.niceList fn(tp)
    tp.ppType.color(colors.colorType)

fun niceList(schemes: list<ktype>, f: (ktype) -> ppTypeEff doc): ppTypeEff list<doc>
  schemes.map(fn(tp) tp.free-type-vars).unions.list.map(extend-nice)
  schemes.map(f)

// Pretty print a type
fun ktp/pretty(t: ktype): <documentation,ppEnvEff,pure,comp-flags,colorSchemeEffect> doc
  with handlePrettyEff
  with niceEnv
  t.ppType

fun tv/pretty(tv: typeVar): <documentation,ppEnvEff,pure,comp-flags,colorSchemeEffect> doc
  with handlePrettyEff
  with niceEnv
  tv.ppTypeVar

fun tcon/pretty(tc: typeCon): <documentation,ppEnvEff,pure,comp-flags,colorSchemeEffect> doc
  with handlePrettyEff
  with niceEnv
  tc.ppTypeCon

fun tsyn/pretty(ts: typeSyn): <documentation,ppEnvEff,pure,comp-flags,colorSchemeEffect> doc
  with handlePrettyEff
  with niceEnv
  ts.ppTypeSyn

fun ppScheme(tp: ktype)
  tp.niceType

fun ppSchemeEffect(tp: ktype)
  match tp
    TFun([], _, _) -> ppSchemeEffect(TForAll([], [], tp))
    TForAll(vars, preds, TFun([], eff, res)) ->
      vars.foreach(extend-nice)
      with overridePrec(precTypeTop)
      val fors = if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(ppTypeVar).angled |.| dot |.| space
      val predDoc = if preds.is-nil then pprint/empty else preds.map(ppPred).commaSep |+| "=> ".text
      val effDoc = if eff.isTypeTotal then pprint/empty else overridePrec(precArrow - 1, {eff.ppType}) |.| space
      val resDoc = res.ppType
      (fors |.| predDoc |.| effDoc |.| resDoc).pparens(prec, precTypeQuant)
    _ -> tp.niceType

fun prettyDefFunType(tp: ktype, pinfos: list<paramInfo>)
  fun ppParam((nm:name, pinfo, tpDoc))
    val x = match pinfo
      Borrow -> "^".text |+| (if nm.is-nil then "_".text else nm.ppName) |+| ": ".text
      _ -> if nm.is-nil then pprint/empty else nm.ppName |+| ": ".text
    x |.| tpDoc
  match tp.ppDeclType(pinfos)
    (Just(params), pre, post) ->
      pre |.| params.map(ppParam).commaSep.parens |+| "->".text |+| post
    (Nothing, pre, post) -> pre |+| "()".text |+| "->".text |+| post

fun ppDeclType(tp: ktype, pinfos: list<paramInfo>)
  match tp
    TForAll(vars, preds, rho) ->
      vars.foreach(extend-nice)
      val (args, _, res) = rho.ppDeclType(pinfos)
      val pre = if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(ppTypeVar).angled |.| space
      (args, pre, res |.| preds.ppPredicates)
    TFun(params, eff, rho) ->
      val pparams = params.map(fn((name, tp')) (name, Own, tp'.ppType))
      (Just(pparams), pprint/empty, if eff.isTypeTotal then pprint/empty else overridePrec(precArrow, {eff.ppType |.| space}) |.| overridePrec(precArrow, {rho.ppType})) 
    _ -> (Nothing, pprint/empty, tp.ppType)

fun pretty(d: dataInfo): <documentation,ppEnvEff,pure,comp-flags,colorSchemeEffect> doc
  with handlePrettyEff
  with niceEnv
  ppDataInfo(d, True, False)

fun ppDataInfo(d: dataInfo, showBody: bool, isExtend: bool)
  d.prettyDataInfo(showBody, False, isExtend)

fun commaSep(d: list<doc>)
  d.punctuate(comma).hsep

fun prettyDataInfo(d: dataInfo, showBody: bool, publicOnly: bool, isExtend: bool)
  if publicOnly && d.vis.is-private then pprint/empty
  else
    val vis = if publicOnly then pprint/empty else d.vis.ppVis
    d.params.foreach(extend-nice)
    val ext = if isExtend then "extend ".keyword else match d.def
      DataDefRec -> "recursive ".text
      DataDefOpen -> "open ".text
      DataDefValue(v) -> ("value" ++ v.show ++ " ").text
      _ -> pprint/empty 
    val sort = match d.sort
      Inductive -> "type".keyword
      CoInductive -> "co type".keyword
      Retractive -> "rec type".keyword
    val params = if d.params.is-nil then pprint/empty else d.params.map(TVar).niceTypes.angled
    val kind = if d.kind == kindStar then pprint/empty else " ::".text |+| d.kind.ppKind(precTop)
    val body = if showBody && d.constrs.is-cons then 
        "{".text |-| d.constrs.map(fn(c) c.prettyConInfo(publicOnly)).vcat.indent(2) |-| "}".text 
      else pprint/empty
    val data = vis |.| ext |.| sort |+| d.name.ppName |.| params |.| body
    data.prettyComment(d.doc)

fun prettyConInfo(c: conInfo, publicOnly: bool)
  if publicOnly && c.vis.is-private then pprint/empty
  else
    fun ppField((_, (name, tp)))
      (if name.is-field-name then pprint/empty else name.ppName |.| ": ".text) |.| tp.ppType
    val vis = if publicOnly then pprint/empty else c.vis.ppVis
    c.existentials.foreach(extend-nice)
    val exists0 = if c.existentials.is-nil then pprint/empty else c.existentials.map(ppTypeVar).angled
    val fields = if c.params.is-nil then pprint/empty else zip(c.paramVis, c.params).map(ppField).commaSep.parens
    val vrepr = c.valueRepr.show.text
    val const = vis |.| "con".keyword |+| c.name.ppName |.| exists0 |.| fields |+| vrepr |+| ":".text |+| c.typeScheme.ppType |.| semi
    const.prettyComment(c.doc)

fun prettyComment(d: doc, comment: string)
  if comment == "" then d else
    val clist = comment.list
    val cmt = if clist.last.unjust == '\n' then clist.init.string else comment
    (cmt.text |-| d).color(colors.colorComment)

fun ppVis(v: visibility): colorSchemeEffect doc
  match v
    Private -> pprint/empty
    Public -> "pub ".keyword

// Synonym info
fun syninfo/pretty(s: synInfo): <documentation,ppEnvEff,pure,comp-flags,colorSchemeEffect> doc
  with handlePrettyEff
  with niceEnv
  ppSynInfo(s)

fun ppSynInfo(s: synInfo, isLocal: bool=False, publicOnly:bool=False, showBody:bool=True)
  if publicOnly && s.vis.is-private then pprint/empty 
  else
    val al = if isLocal then "local alias".keyword else s.vis.ppVis |.| "alias".keyword
    val params = if s.params.is-nil then pprint/empty else s.params.map(TVar).niceTypes.angled
    val kind = if s.kind == kindStar then pprint/empty else " ::".text |+| s.kind.ppKind(precTop)
    val body = if !showBody then pprint/empty else "=".keyword |+| s.t.niceType
    val syn = al |+| s.name.ppName |.| params |.| kind |+| body |+| "=".text |+| pretty(s.rank)
    syn.prettyComment(s.doc)

fun ppType(tp: ktype)
  val t = match tp
    TForAll(vars, preds, t) ->
      val p = prec
      vars.foreach(extend-nice)
      val d = (if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(fn(v) v.ppTypeVar).angled |.| space)
      val d' = d |.| t.ppType |.| preds.ppPredicates
      d'.pparens(p, precTypeQuant)
    TFun(args, eff, res) -> ppFun("->".text, args, eff, res)
    TVar(tv as TypeVar(_, _, Bound)) ->
      match ranked.lookup(tv)
        Nothing -> tv.ppTypeVar
        Just(f) -> f(prec)
    TVar(tv) -> tv.ppTypeVar
    TCon(cv) -> ppTypeCon(cv)
    TApp(TCon(c), [_, _]) | c.name == nameEffectExtend ->
      val (ls, tl) = tp.shallowExtractEffectExtend
      val tldoc = if tl == effectEmpty then pprint/empty else "|".text |.| overridePrec(precTypeTop, {tl.ppType})
      val isCoreIface = ppEnv.coreIface
      val isTailEmpty = tl == effectEmpty 
      val doc = match ls
        [l] | isTailEmpty && !isCoreIface -> overridePrec(precTypeAtom, {l.ppType})
        _ -> "<".text |.| ls.map(fn(l) overridePrec(precTypeTop, {l.ppType})).punctuate(comma).hcat |.| tldoc |.| ">".text
      doc.color(colors.colorEffect)
    TApp(TCon(c), [eff, res]) | c.name == nameTpDelay ->
      "$".text |+| (if eff.isTypeTotal then pprint/empty else overridePrec(precArrow, {eff.ppType}) |.| space) |.|
      overridePrec(precArrow, {res.ppType})
    TApp(TCon(c), [arg]) ->
      if c.name == nameTpOptional && colorizing then
        "?".text |.| overridePrec(precTypeAtom, {arg.ppType})
      elif c.name == nameTpHandled || c.name == nameTpHandled1 && !ppEnv.coreIface then
        arg.ppType
      else
        match tp
          TApp(TCon(TypeCon(nm)), args) | nm.is-name-tuple -> args.map(fn(t) overridePrec(precTypeTop, {t.ppType})).commaSep.parens
          TApp(f, args) ->
            val fdoc = overridePrec(precTypeAtom, {f.ppType})
            val argsdoc = match args 
              Nil -> pprint/empty
              Cons(targ, rest) -> 
                val argsDoc = args.map(fn(a) overridePrec(precTypeTop, {a.ppType})).angled
                if rest.is-nil then argsDoc.colorByKind(targ.kind, id) else argsDoc
            (fdoc |.| argsdoc).pparens(prec, precApp)
    // TODO: this is duplicated above due to issues with limitations in guards
    TApp(f, args) ->
      val fdoc = overridePrec(precTypeAtom, {f.ppType})
      val argsdoc = match args 
        Nil -> pprint/empty
        Cons(arg, rest) -> 
          val argsDoc = args.map(fn(a) overridePrec(precTypeTop, {a.ppType})).angled
          if rest.is-nil then argsDoc.colorByKind(arg.kind, id) else argsDoc
      (fdoc |.| argsdoc).pparens(prec, precApp)
    TSyn(syn, args, tp) ->
      overridePrec(precTop, {tp.ppType}).ppSynonym(syn, args)
  t.color(colors.colorType)

fun ppPredicates(preds: list<pred>)
  if preds.is-nil then pprint/empty
  else
    " with".keyword |+| preds.map(ppPred).hcat.align

fun ppFun(arrow, args, eff, result)
  args.map(fn(p) overridePrec(precTypeTop, {p.ppParam})).punctuate(comma).hsep.parens.pparens(prec, precTypeArrow) |+|
  (if eff.isTypeTotal then arrow else arrow |+| overridePrec(precTypeArrow, {eff.ppType})) |+|
  overridePrec(precTypeArrow, {result.ppType})

fun ppParam((nm: name, tp: ktype))
  val name = if !(nm.is-nil || nm.is-field-name || nm.is-wildcard) then
      nm.unqualify.ppNameEx.color(colors.colorParameter) |.| ":".text
    else
      pprint/empty
  name |.| tp.ppType

fun ppName(nm: name)
  nm.ppNameEx.color(colors.colorSource)

fun ppTypeName(nm: name)
  nm.ppNameEx.color(colors.colorType)

fun ppNameEx(n: name)
  if ppEnv.fullNames then n.pretty
  elif n.qualifier == moduleContext || n.is-name-tuple || 
    ((n.qualifier == nameSystemCore || n.qualifier == nameCoreTypes) && !ppEnv.coreIface) then
    n.unqualify.pretty
  else
    importsMap.get-alias(n).pretty

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
    (if ppEnv.expandSynonyms then " == ".text |.| ts.rank.pretty |+| tpdoc else pprint/empty)
  if ppEnv.expandSynonyms then
    nm.parens
  elif args.is-nil then
    nm
  else
    nm.pparens(prec, precTypeApp)

fun ppTypeVar(tv: typeVar)
  val fl = match tv.flavour
    Meta -> "_".text
    Skolem -> if ppEnv.coreIface then "__".text else "$".text
    _ -> pprint/empty
  val nm = fl |.| get-nice-doc(tv) |.| (if ppEnv.showIds then text("=" ++ tv.tid.show) else pprint/empty)
  nm.wrapKind(tv.kind).colorByKindDef(tv.kind, colorTypeVar)

fun ppTypeCon(tc: typeCon)
  tc.name.ppNameEx.wrapKind(tc.kind).colorByKindDef(tc.kind, colorTypeCon)

fun ppTypeSyn(ts: typeSyn)
  ts.name.ppNameEx.wrapKind(ts.kind).colorByKindDef(ts.kind, colorTypeCon)

fun colorByKindDef(d: doc, k: kind, defcolor: (colorScheme -> <prettyTypeEff,colorSchemeEffect> color))
  d.colorByKind(k, fn(d') d'.color(defcolor(colors)))

fun colorByKind(d: doc, k: kind, defcolor: (doc -> <prettyTypeEff,colorSchemeEffect> doc))
  match k.colorForKind
    Just(c) -> d.color(c)
    Nothing -> defcolor(d)

fun colorForKind(k: kind)
  if k == kindEffect || k == kindLabel || k == kind-fun(kindHeap, kindLabel) then
    Just(colors.colorEffect)
  elif k == kindHeap || k == kindScope then
    Just(colors.colorEffect)
  else Nothing

fun wrapKind(d: doc, k: kind)
  if ppEnv.showKinds && k != kindStar then
    parens(d.color(colors.colorType) |+| "::".text |+| k.ppKind(kind/pretty/precTop)).color(colors.colorKind)
  else d
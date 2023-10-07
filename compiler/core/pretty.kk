import compiler/common/name
import compiler/common/color-scheme
import compiler/common/syntax
import compiler/common/nice
import compiler/common/name-collections
import compiler/lib/pprint
import compiler/core/core
import compiler/kind/kind
import compiler/kind/pretty
import compiler/kind/synonyms
import compiler/kind/importmap
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/platform/config
import newstd/data/linearmap

// Show pretty names rather than numbers

val prettyNames = True

fun source(d: doc)
  d.color(colors.colorSource)

// TODO: Show instances


// Pretty printers

  // val showKinds: bool
  // val showIds: bool // show id numbers
  // val expandSynonyms: bool
  // val ranked: tvScheme
  // val moduleContext: name // module in which we pretty print
  // val importsMap: importmap // import aliases
  // val fullNames: bool

fun setEnv(env: ppEnv, f: () -> <ppEnvEff|e> a): <ppEnvEff|e> a
  with override val ppEnv = env
  f()

fun noVis(f)
  setEnv(ppEnv(coreShowVis=False), f)

fun noVisShowDef(f)
  setEnv(ppEnv(coreShowVis=False, coreShowDef=True),f)

fun prettyCore(target: target, inlineDefs: list<inlineDef>, c as Core(name, imports, fixDefs, typeDefGroups, defGroups, externals, doc): core)
  val importedSyns = c.extractImportedSynonyms()
  val extraImports = extractImportsFromSynonyms(imports, importedSyns)
  val allDefs = defGroups.flatten
  val allTypeDefs = typeDefGroups.flatten
  fun separator(msg)
    if !ppEnv.coreIface then [] else [" ".text, "//----------------------".text, ("//#kki: " ++ msg).text, " ".text]
  with override
    val importsMap = importsMap.extendImportMap(extraImports)
    val ranked = ranked
    val moduleContext = moduleContext
  val p0 = ppEnv
  with override
    val ppEnv = p0(showKinds = p0.showKinds || p0.coreIface, coreShowDef = !p0.coreIface, coreShowTypes = p0.coreIface || p0.coreShowTypes)
  val p = ppEnv(expandSynonyms = False)
  val px = ppEnv(showKinds = False, expandSynonyms = True)
  val coreDoc = "module".keyword |+| (if ppEnv.coreIface then "interface".text else empty) |.|
    name.prettyDefName |-|
    vcat([
      "import declarations".separator,
      setEnv(px, {imports.map(prettyImport)}),
      "external imports".separator,
      setEnv(px, {externals.map(fn(e) e.prettyExternalImport(target))}),
      "fixity declarations".separator,
      setEnv(px, {fixDefs.map(prettyFixDef)}),
      "local imported aliases".separator,
      setEnv(px, {importedSyns.map(prettyImportedSyn)}),
      "type declarations".separator,
      setEnv(px, {allTypeDefs.map(prettyTypeDef)}),
      "declarations".separator,
      setEnv(p, {allDefs.map(prettyDef)}), // TODO: is this and the next env wrong?
      "external declarations".separator,
      setEnv(p, {externals.map(prettyExternal)}),
      "inline definitions".separator,
      (
        if !ppEnv.coreIface || inlineDefs.is-nil then [] 
        else 
          ["//.inline-section".text] ++ inlineDefs.map(prettyInlineDef)
      ) 
    ].concat)
  coreDoc.prettyComment(doc)

fun prettyImport(Kimport(name, pkg, vis, _): kimport)
  prettyVis(vis, "import".keyword |+| importsAlias(importsMap, name).pretty |+| "=".text |+|
    name.prettyName |+| "=".text |+| LitString(pkg).prettyLit |.| semi
    )

fun prettyExternalImport(e: external, t: target)
  match e
    External -> empty
    ExternalImport(imports) ->
      match lookupTarget(t, imports)
        Nothing -> empty
        Just(kvals0) ->
          fun prettyKeyval((k, v))
            LitString(k).prettyLit |.| "=".text |.| LitString(v).prettyLit |.| semi
          match kvals0.filter(fn((key, _)) key != "include-inline" && key != "header-include-inline")
            [] -> empty
            keyvals ->
              "extern import".keyword |+| "{".text |-|
                tab(t.ppTarget |+| "{".text |-| tab(keyvals.map(prettyKeyval).vcat) |-| "};".text) |-| "};".text
  
fun prettyFixDef(FixDef(nm, fixity): fixDef)
  val d = match fixity
    FixInfix(f, assoc) ->
      val adoc = match assoc
        AssocLeft -> "infixl".text
        AssocRight -> "infixr".text
        AssocNone -> "infix".text 
      adoc |+| f.pretty
    FixPrefix -> "prefix".text
    FixPostfix -> "postfix".text
  d |+| nm.prettyDefName |.| semi

fun prettyImportedSyn(si: synInfo)
  si.ppSynInfo(True, False, True) |.| semi

fun prettyExternal(ex: external)
  match ex
    ExternalImport -> empty
    External(name, tp, pinfos, body, vis, _, _, doc) ->
      if ppEnv.coreIface && name.isHiddenExternalName then empty
      else
        // TODO:
        fun prettyEntry((t:target, c: string))
          t.ppTarget |.| "inline".keyword |+| LitString(c).prettyLit |.| semi
        val entriesDoc = match body
          [(DefaultTarget, content)] -> "= inline".keyword |+| LitString(content).prettyLit |.| semi
          _ -> "{".text |-| tab(body.map(prettyEntry).vcat) |-| "};".text
        val d = "extern".keyword |+| name.prettyDefName |+| ":".text |+| tp.prettyDefFunType(pinfos) |+| entriesDoc
        prettyVis(vis, d).prettyComment(doc)

fun ppTarget(t: target)
  match t
    DefaultTarget -> empty
    CS -> "cs ".text
    JS -> "js ".text
    C -> "c ".text

fun prettyTypeDefGroup(tdg: typeDefGroup)
  vcat(tdg.map(prettyTypeDef))

fun prettyTypeDef(td: typeDef)
  match td
    Synonym(synInfo) -> synInfo.ppSynInfo(False, True, True) |.| semi
    Data(dataInfo, isExtend) -> dataInfo.prettyDataInfo(True, False, isExtend) |.| semi 

fun prettyDefGroup(dg: defGroup)
  match dg
    DefNonRec(d) -> d.prettyDefX(False)
    DefRec(ds) -> "rec {".text |+| align(ds.prettyDefs) / "}".text

fun prettyDefs(defs: list<def>)
  defs.map(prettyDef).vcat

fun prettyInlineDef(InlineDef(name, expr, isRec, inlkind, cost, sort, specArgs): inlineDef)
  val rdoc = if isRec then "recursive ".keyword else empty
  val prettySpecArgs = specArgs.map(fn(s) if s then '*' else '_').string.text.dquotes
  val specdoc = if specArgs.is-nil then empty else "specialize ".keyword |.| prettySpecArgs |.| " ".text 
  val inl = if cost <= 0 || inlkind.is-inlineAlways then "inline ".keyword else empty
  val pidoc = match sort
    DefFun(pinfos) -> if pinfos.any(fn(p) p.is-borrow) then "borrow".keyword |+| dquotes(pinfos.map(fn(i) if i.is-borrow then '^' else '_').string.text) |.| " ".text else empty
    _ -> empty
  val nm = if name.isNil then "_".text else name.prettyDefName
  rdoc |.| specdoc |.| inl |.| pidoc |.| sort.showFull.keyword |+|
    nm |+| ("// inline size: " ++ cost.show).text |.| linebreak |.|
    ("=".text |+| noVisShowDef({expr.prettyExpr})).indent(2) |.| semi
  
fun prettyDef(d: def)
  d.prettyDefX(True)

fun prettyDefX(Def(name, scheme, expr, _, sort, _, _, doc): def, isRec: bool)
  val ppBody = noVis({expr.prettyExpr})
  val d = sort.showFull.keyword |+| (if name.isNil && ppEnv.coreShowDef then "_".text else name.prettyDefName) |+|
    ":".text |+| (match sort {DefFun(pinfos) -> scheme.prettyDefFunType(pinfos); _ -> scheme.prettyType}) |.|
    (if !ppEnv.coreShowDef then empty else linebreak |.| ("=".text |+| ppBody).indent(2) |.| semi)
  d.prettyComment(doc)

fun prettyVis(vis: visibility, d: doc)
  if !ppEnv.coreShowVis then d
  else
    match vis
      Public -> "pub".keyword |+| d
      Private -> d

fun prettyType(tp: ktype)
  prettyTypes([tp]).head.unjust

fun prettyTypes(tps: list<ktype>)
  niceTypes(tps)

fun prettyKind(pre: string, k: kind)
  if k == kindStar then empty else pre.text |.| k.ppKind(precTypeTop)

// Expressions
fun tab(d: doc)
  d.indent(2)

// Core lambda calculus
fun prettyExpr(ex: expr)
  match ex
    Lam(tnames, eff, expr) ->
      val doc = "fn".keyword |.| (if eff.isTypeTotal then empty else overridePrec(precTypeTop, {"<".text |.| eff.prettyType |.| ">".text}).color(colors.colorType)) |.|
        overridePrec(precTypeTop, {tnames.map(prettyTName).tupled}) |.| "{".text |--|
        tab(expr.prettyExpr |.| semi) |--| "}".text
      doc.pparens(prec, precTypeArrow)
    Var(tname) ->
      tname.prettyVar
    App(a, args) ->
      overridePrec(precTypeApp, {a.prettyExpr |.| args.map(fn(e) e.prettyExpr).tupled}).pparens(prec, precTypeApp)
    // Type abstraction / application
    TypeLam(tvs, expr) ->
      if prettyNames then
        tvs.foreach(extendNice)
      val doc = overridePrec(precTypeTop, {"forall".text |.| tvs.map(fn(tv) tv.prettyTypeVar).angled |+| ".".text |+| expr.prettyExpr})
      doc.pparens(prec, precTypeArrow)
    TypeApp(expr, tps) ->
      if !ppEnv.coreShowTypes then expr.prettyExpr
      else
        val dtps = overridePrec(precTypeTop, {tps.map(fn(tp) tp.prettyType)}).angled
        val de = overridePrec(precTypeApp - 1, {expr.prettyExpr})
        (de |.| dtps).pparens(prec, precTypeApp)
    // Literals and Contants
    Con(tname) -> tname.prettyVar
    ELit(l) -> l.prettyLit
    Let([DefNonRec(Def(x, tp, e))], e') ->
      val exprDoc = e.prettyExpr |.| semi
      vcat([
        "val".keyword |+| ((if x.isNil then "_".text else x.prettyDefName) |+| tp.prettyType |-| "=".text |+| exprDoc).hang(2),
        e'.prettyExpr
      ]) 
    Let(defgs, e) ->
      vcat([defgs.map(prettyDefGroup).vcat.align, e.prettyExpr])
    // Case expressions
    Case(exprs, branches) -> 
      val doc = "match".keyword |+| tupled(overridePrec(precTypeAtom, {exprs.map(fn(e) e.prettyExpr)})) |+| "{".text |--|
        tab(branches.prettyBranches) |--| "}".text
      doc.pparens(prec, precTypeTop) 

fun prettyVar(tn: tName)
  tn.getName.prettyName

// Case branches

fun prettyBranches(bs: list<branch>)
  bs.map(prettyBranch).vcat

fun prettyBranch(Branch(patts, guards): branch)
  val pats = overridePrec(precTypeApp, {prettyPatterns(patts)})
  hsep(pats.punctuate(comma)) |.| linebreak |.| indent(vcat(guards.map(prettyGuard)), 2) |.| semi 

fun prettyGuard(Guard(test, expr): guard)
  (if test.isTrue then empty else " |".text |+| overridePrec(precTop, {test.prettyExpr})) |+|
  " ->".text |+| overridePrec(precTop, {expr.prettyExpr})

fun prettyPatterns(pats: list<pattern>)
  pats.map(prettyPattern)

fun prettyPatternType(pat: pattern, tp: ktype)
  val doc = overridePrec(prec - 1, {pat.prettyPattern})
  doc |.| (if ppEnv.coreShowTypes then " :".text |+| tp.prettyType else empty)

fun prettyConName(tname: tName)
  tname.getName.pretty

fun prettyPattern(pat: pattern)
  match pat
    PatCon(tname, args, _, targs, exists0, resTp, _, skip) ->
      exists0.foreach(extendNice)
      val docs = args.zip(targs).foldr([], fn((a, t), l) l ++ [a.prettyPatternType(t)])
      parens(
        (if skip then ".skip".keyword else empty) |.|
        tname.prettyConName |.| (if exists0.is-nil then empty else angled(exists0.map(ppTypeVar))) |.|
        tupled(docs) |+| resTp.prettyType |.| space
      )
    PatVar(tname, PatWild) -> 
      parens(tname.prettyTName)
    PatVar(tname, pat) ->
      parens(overridePrec(prec - 1, {pat.prettyPattern}) |+| "as".keyword |+| tname.prettyTName)
    PatWild -> "_".text
    PatLit(l) -> prettyLit(l)


// Literals
fun prettyLit(l: lit)
  match l
    LitInt(i) -> i.show.text.color(colors.colorNumber)
    LitFloat(f) -> f.show.text.color(colors.colorNumber)
    LitChar(c) -> ("'" ++ showXChar(c.head-char.unjust) ++ "'").text.color(colors.colorString)
    LitString(s) -> ("\"" ++ s.list.map(showXChar).join ++ "\"").text.color(colors.colorString)

fun showXChar(c: char): string
  if c >= ' ' && c <= '~' && c != '\"' && c != '\'' && c != '\\' then c.string
  else
    val n = c.int
    if n < 256 then "\\x" ++ n.show-hex(2)
    elif n < 65536 then "\\u" ++ n.show-hex(4)
    else "\\U" ++ n.show-hex(6)

// Pretty-printers for non-core terms

fun prettyTName(TName(nm, t): tName)
  nm.prettyName |.| ":".text |+| t.ppType

fun prettyName(n: name)
  if n.isQualified then
    (n.nameModule ++ "/").text.color(colors.colorNameQual) |.| 
      n.unqualify.pretty.color(colors.colorSource)
  else n.pretty.color(colors.colorSource)

fun prettyDefName(n: name)
  val cn = n.unqualify
  val (nm, post) = cn.canonicalSplit
  val s = nm.show
  val pre = match s.list
    Nil -> empty
    Cons(c) -> if c.is-alpha || c.is-digit || c == '_' || c == '(' || c == ')' then s.text else s.text.parens
  if post == "" then pre else pre |.| post.text

fun ppOperatorName(n: name)
  val s = n.unqualify.show
  val fmted = match s.list
    Nil -> empty
    Cons(c) -> if c.is-alpha || c.is-digit then ("`" ++ s ++ "`").text else s.text
  fmted.color(colors.colorSource)

val prettyTypeVar = ppTypeVar



// Extend an import map with nice aliases for a set of new imports
fun extendImportMap(im: importmap, imps: list<kimport>): importmap
  imps.foldr(im) fn(i, im')
    val fullName = i.importName
    match im'.importsExtend(fullName, fullName)
      Just(new) -> new
      Nothing -> im'

// extract all qualifiers in synonyms: it can be the case that a type synonym
// refers to a type defined in a non-imported module and we need to add it to the
// imports of the .kki file. (no need to add it to the generated code since
// javascript does not use types, while c-sharp does not use import declarations but fully
// qualified names all the time)

fun extractType(tp: ktype)
  match tp
    TSyn(syn, args, body) -> Cons(syn.name.qualifier, Cons(body,args).extractTypes)
    TApp(c, args) -> Cons(c, args).extractTypes
    TFun(args, eff, res) -> Cons(res, Cons(eff, args.map(snd))).extractTypes
    TForAll(_, _, b) -> b.extractType
    TCon(tc) -> [tc.name.qualifier]
    TVar -> []

fun extractTypes(tps: list<ktype>)
  tps.map(extractType).concat

fun extractImportsFromSynonyms(imps: list<kimport>, syns: list<synInfo>)
  val impNames = imps.map(importName)
  fun extractSyn(syn: synInfo)
    Cons(syn.name.qualifier, syn.t.extractType)
  val quals = syns.map(extractSyn).concat.filter(fn(nm) !impNames.any(fn(n) n == nm))
  quals.map(fn(nm) Kimport(nm, "", Private, "")) // TODO: import path?

// extract from type signatures the synonyms so we can compress .kki files
// by locally defining imported synonyms
fun extractSynonym(tp: ktype): pure name-map<synInfo>
  match tp
    TSyn(syn, args, body) ->
      val syns = Cons(body, args).extractSynonyms
      match syn.info
        Just(i) -> syns.set(i.name, i)
        Nothing -> syns
    TApp(c, args) -> Cons(c, args).extractSynonyms
    TFun(args, eff, res) -> Cons(res, Cons(eff, args.map(snd))).extractSynonyms
    TForAll(_, _, b) -> b.extractSynonym
    _ -> emptySynonyms

fun extractSynonyms(tps: list<ktype>): pure name-map<synInfo>
  tps.map(extractSynonym).foldr(emptySynonyms, fn(s1, s2) s2.union(s1))

fun extractImportedSynonyms(c: core)
  c.extractSignatures.extractSynonyms.list.map(snd).filter(fn(i:synInfo) c.coreName != i.name.qualifier)

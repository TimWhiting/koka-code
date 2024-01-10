import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/color-scheme
import compiler/type/type
import compiler/type/pretty
import compiler/core/core
import compiler/common/name-collections
import compiler/lib/pprint
import newstd/data/linearmap
import newstd/data/linearset
import newstd/data/sort
import compiler/common/failure
import compiler/platform/config
import compiler/core/corevar
import compiler/type/typevar

pub infixr 5 (|->)

type nameInfo
  InfoVal(vis: visibility, cname: name, typ: scheme, range: range, isVar: bool)
  InfoFun(vis: visibility, cname: name, typ: scheme, arity: (int, int), fipt: fipT, range: range)
  InfoCon(vis: visibility, typ: scheme, repr: conRepr, conInfo: conInfo, range: range)
  InfoExternal(vis: visibility, cname: name, typ: scheme, format: list<(target, string)>, fipt: fipT, range: range)
  InfoImport(vis: visibility, typ: scheme, nameAlias: name, fullName: name, range: range)

fun (==)(ni1: nameInfo, ni2: nameInfo)
  range/(==)(ni1.range, ni2.range)

fun show(ni: nameInfo): div string
  match ni
    InfoVal(vis, cname, typ, range, isVar) -> "InfoVal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-full-range(range) ++ ", " ++ show(isVar) ++ ")"
    InfoFun(vis, cname, typ, arity, fipt, range) -> "InfoFun(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-tuple(arity, show, show) ++ ", " ++ show(fipt) ++ ", " ++ show-full-range(range) ++ ")"
    InfoCon(vis, typ, repr, conInfo, range) -> "InfoCon(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(repr) ++ ", " ++ show(conInfo) ++ ", " ++ show-full-range(range) ++ ")"
    assumption/InfoExternal(vis, cname, typ, format, fipt, range) -> "InfoExternal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-list(format, fn(s) s.show-tuple(show, fn(x) x)) ++ ", " ++ show(fipt) ++ ", " ++ show-full-range(range) ++ ")"
    InfoImport(vis, typ, nameAlias, fullName, range) -> "InfoImport(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(nameAlias) ++ ", " ++ show(fullName) ++ ", " ++ show-full-range(range) ++ ")"

fun canonicalName(info: nameInfo, name: name)
  match info
    InfoVal(cname=c) -> c
    InfoFun(cname=c) -> c
    assumption/InfoExternal(cname=c) -> c
    _ -> name

fun isInfoValFunExt(info)
  match info
    InfoVal() -> True
    InfoFun() -> True
    assumption/InfoExternal() -> True
    _ -> False

fun isInfoFunOrExternal(info)
  match info
    InfoFun() -> True
    assumption/InfoExternal() -> True
    _ -> False

fun fipT(info: nameInfo)
  match info
    InfoFun(fipt=fipt) -> fipt
    assumption/InfoExternal(fipt=fipt) -> fipt
    _ -> noFip

fun element(info: nameInfo)
  match info
    InfoCon() -> "constructor"
    InfoImport() -> "import"
    _ -> "identifier"

fun isVisible(info: nameInfo)
  info.vis.is-public

fun coreVarInfo(info: nameInfo)
  match info
    InfoVal -> InfoNone
    InfoFun(arity=(m,n)) -> InfoArity(m, n)
    assumption/InfoExternal(format=f) -> compiler/core/core/InfoExternal(f)
    _ -> throw("type/assumption coreVarInfo")

fun coreExpr(info: nameInfo, qname: name)
  match info
    InfoVal(_, cname, tp) -> Var(TName(cname, tp), InfoNone)
    InfoFun(_, cname, tp, (m, n), _) -> Var(TName(cname, tp), InfoArity(m ,n))
    InfoCon(_, tp, repr) -> Con(TName(qname, tp), repr)
    assumption/InfoExternal(_, cname, tp, format) -> Var(TName(cname, tp), compiler/core/core/InfoExternal(format))
    _ -> throw("type/assumption coreExpr")

// Names to type schemes.
// Due to overloading there may be multiple entries for the same qualified name

alias gamma = name-map<list<(name, nameInfo)>>
val empty = linearMap([])

fun gammaList(g: gamma): list<(name, nameInfo)>
  g.list.map(snd).concat.sortBy(fn((n, _), (n2, _)) n.compare(n2))

fun schemes(g: gamma): list<scheme>
  g.gammaList.map(fn(n) n.snd.typ)

fun single(name: name, ni: nameInfo)
  empty.set(name, [(name, ni)])

fun gammaExtend(g: gamma, name: name, ni: nameInfo)
  g.update(name.unqualify, [(name, ni)], fn(old, new) old ++ new)

fun gammaLookupCanonical(g: gamma, name: name)
  g.gammaLookupQ(name.nonCanonicalName).filter(fn(ni) ni.canonicalName(nameNil) == name)

fun gammaLookupExactCon(g: gamma, name: name)
  g.gammaLookupQ(name).filter(is-infoCon)

fun gammaLookupQ(g: gamma, name: name)
  match g.maybeGet(name.unqualify)
    Nothing -> []
    Just(xs) -> xs.filter(fn(n) n.fst == name).map(snd)

fun gammaLookup(g: gamma, name: name)
  match g.maybeGet(name.unqualify)
    Nothing -> []
    Just(xs) ->
      val ys = if name.isQualified then
                  xs.filter(fn((n, _)) n == name || name.nameCaseEqual(n))
                else
                  xs
      ys.filter(fn((_, info)) info.isVisible)

fun gammaMap(g: gamma, f: (nameInfo -> nameInfo)): gamma
  g.map(fn(k, xs) (k, xs.map(fn((n, ni)) (n, f(ni)))))

fun gammaRemove(g: gamma, name: name)
  g.remove(name.unqualify)

fun gammaUnion(g1: gamma, g2: gamma)
  g2.unionWith(g1, fn(xs1, xs2) xs1 ++ xs2)

fun gammaUnions(gs: list<gamma>)
  gs.foldl(compiler/type/assumption/empty, gammaUnion)

fun gammaFilter(g: gamma, mod: name)
  g.filter(fn(k, _) k.qualifier == mod)

fun gammaNames(g: gamma)
  g.list.map(fst)

fun gammaPublicNames(g: gamma)
  g.filter(fn(n, nis) nis.all(fn((_, ni)) ni.isVisible && !n.isHiddenName)).list.map(fst)

fun extractGammaImports(imports: list<(name,name)>, modName: name): gamma
  val modAlias = modName.nameId.list.reverse.take-while(fn(a) a != '.').reverse.string.newName
  imports.map(extractImport).gammaUnions.gammaExtend(modAlias, InfoImport(Private, typeVoid, modAlias, modName, rangeNull))

fun extractImport((name, qname))
  single(name, InfoImport(Private, typeVoid, name, qname, rangeNull))

fun extractGamma(isValue: (dataInfo -> bool), privateAsPublic: bool, c: core): <exn, compFlags> gamma
  fun updateVis(vis)
    match vis
      Public -> Public
      _ -> if privateAsPublic then Public else vis
  gammaUnions([
    c.defs.map(fn(dg) dg.extractDefGroup(updateVis)).gammaUnions,
    c.externals.map(fn(ex) ex.extractExternal(updateVis)).gammaUnions,
    c.typeDefs.map(fn(td) td.extractTypeDefGroup(isValue, updateVis)).gammaUnions
  ])

fun extractTypeDefGroup(td: typeDefGroup, isValue: (dataInfo -> bool), updateVis)
  td.map(fn(d) extractTypeDef(isValue, updateVis, d)).gammaUnions

fun extractTypeDef(isValue: (dataInfo -> bool), updateVis, td: typeDef)
  fun extractConInfo((info, repr): (conInfo, conRepr))
    single(info.name, InfoCon(updateVis(info.vis), info.typeScheme, repr, info, info.range))
  match td
    Data(dataInfo, _) -> zip(dataInfo.constrs, dataInfo.dataRepr(isValue).snd).map(extractConInfo).gammaUnions
    _ -> assumption/empty

fun extractDefGroup(d: defGroup, updateVis)
  match d
    DefRec(defs) -> defs.map(fn(v) extractDef(v, updateVis)).gammaUnions
    DefNonRec(v) -> extractDef(v, updateVis)

fun extractDef(d: def, updateVis)
  single(d.defName.nonCanonicalName, createNameInfoX(updateVis(d.vis), d.defName, d.sort, d.nameRange, d.ktype))

fun coreDefInfo(d: def)
  (d.defName.nonCanonicalName, createNameInfoX(d.vis, d.defName, if d.sort.is-defFun && !d.isTopLevel then DefVal else d.sort, d.nameRange, d.ktype))

fun createNameInfoX(vis, name, sort, rng, tp)
  match sort
    DefFun(_, fipT) -> InfoFun(vis, name, tp, tp.arity, fipT, rng)
    DefVar -> InfoVal(vis, name, tp, rng, True)
    _ -> InfoVal(vis, name, tp, rng, False)

fun arity(tp: ktype): <compFlags, exn> (int, int)
  match tp.expandSyn
    TForAll(tvars, _, t) ->
      match t.expandSyn
        TFun(pars) -> (tvars.length, pars.length)
        _ -> (tvars.length, -1)
    TFun(pars) -> (0, pars.length)
    _ -> fail("type/assumption createNameInfoX")

fun extractExternal(external: external, updateVis)
  match external
    External(name, tp, _, body, vis, fipT, nameRng, _) ->
      single(name.nonCanonicalName, InfoExternal(updateVis(vis), name, tp, body, fipT, nameRng))
    _ -> assumption/empty

// TODO: PRETTY PRINT && substitutions

fun freeTypeVars(g: gamma): pure tvs
  g.schemes.map(freeTypeVars).unions

fun boundTypeVars(g: gamma): pure tvs
  g.schemes.map(boundTypeVars).unions

fun freeTypeVars(info: nameInfo): pure tvs
  info.typ.freeTypeVars

fun boundTypeVars(info: nameInfo): pure tvs
  info.typ.boundTypeVars

fun mapType(ni: nameInfo, f: (ktype) -> e ktype): e nameInfo
  match ni
    InfoVal(vis, cname, typ, range, isVar) -> InfoVal(vis, cname, f(typ), range, isVar)
    InfoFun(vis, cname, typ, arity, fipt, range) -> InfoFun(vis, cname, f(typ), arity, fipt, range)
    InfoCon(vis, typ, repr, conInfo, range) -> InfoCon(vis, f(typ), repr, conInfo, range)
    assumption/InfoExternal(vis, cname, typ, format, fipt, range) -> assumption/InfoExternal(vis, cname, f(typ), format, fipt, range)
    InfoImport(vis, typ, nameAlias, fullName, range) -> InfoImport(vis, f(typ), nameAlias, fullName, range)

fun (|->)(sub: sub, g: gamma): pure gamma
  g.map(fn(n, nis) (n, nis.map(fn((n1, ni)) (n1, sub |-> ni))))

fun (|->)(sub: sub, ni: nameInfo): pure nameInfo
  ni.mapType(fn(t) sub |-> t)

fun ppGammaInternal(g: gamma, showHidden: bool)
  val nameSchemes = g.gammaList.map(fn((n, i)) (n, i.typ))
  val maxWidth = nameSchemes.map(fn((n, _)) n.show.count).maximum(0).min(12)
  fun nice(scheme: ktype)
    align(niceTypes([scheme]).head.unjust)
  vcat(nameSchemes.filter(fn((n, _)) showHidden || !n.isHiddenName).map(fn((n, s))
    fill(n.showPlain.text |.| typeColon().color(colors.colorSep) |+| align(nice(s)), maxWidth)
  ))

fun ppGamma(g: gamma)
  ppGammaInternal(g, False)

fun ppGammaHidden(g: gamma)
  ppGammaInternal(g, True)

fun pretty(g: gamma): <ppTypeEff> doc
  ppGamma(g)

fun showGamma(g: gamma): ppTypeEff string
  pretty(g).show
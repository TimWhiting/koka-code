import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/color-scheme
import compiler/type/type
import compiler/type/pretty
import compiler/core/core
import compiler/common/name-collections
import compiler/lib/pprint
import compiler/common/failure
import compiler/platform/config
import compiler/core/corevar
import compiler/type/typevar
import std/data/linearmap
import std/data/linearset
import std/os/path
import newstd/data/sort

pub infixr 5 (|->)

type nameInfo
  InfoVal(vis: visibility, cname: name, typ: scheme, range: range, isVar: bool, doc: string)
  InfoFun(vis: visibility, cname: name, typ: scheme, arity: (int, int), fipt: fipT, range: range, doc: string)
  InfoCon(vis: visibility, typ: scheme, repr: conRepr, conInfo: conInfo, range: range, doc: string)
  InfoExternal(vis: visibility, cname: name, typ: scheme, format: list<(target, string)>, fipt: fipT, range: range, doc: string)
  InfoImport(vis: visibility, typ: scheme, nameAlias: name, fullName: name, range: range)

fun (==)(ni1: nameInfo, ni2: nameInfo)
  range/(==)(ni1.range, ni2.range)

fun show(ni: nameInfo): div string
  match ni
    InfoVal(vis, cname, typ, range, isVar) -> "InfoVal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-full-range(range, "".path) ++ ", " ++ show(isVar) ++ ")"
    InfoFun(vis, cname, typ, arity, fipt, range) -> "InfoFun(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-tuple(arity, show, show) ++ ", " ++ show(fipt) ++ ", " ++ show-full-range(range, "".path) ++ ")"
    InfoCon(vis, typ, repr, conInfo, range) -> "InfoCon(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(repr) ++ ", " ++ show(conInfo) ++ ", " ++ show-full-range(range, "".path) ++ ")"
    assumption/InfoExternal(vis, cname, typ, format, fipt, range) -> "InfoExternal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-list(format, fn(s) s.show-tuple(show, fn(x) x)) ++ ", " ++ show(fipt) ++ ", " ++ show-full-range(range, "".path) ++ ")"
    InfoImport(vis, typ, nameAlias, fullName, range) -> "InfoImport(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(nameAlias) ++ ", " ++ show(fullName) ++ ", " ++ show-full-range(range, "".path) ++ ")"

fun info-sort(ni: nameInfo)
  match ni
    InfoVal -> "val"
    InfoFun -> "fun"
    assumption/InfoExternal -> "external"
    InfoCon -> "con"
    InfoImport -> "module"

fun canonical-name(info: nameInfo, name: name)
  match info
    InfoVal(cname=c) -> c
    InfoFun(cname=c) -> c
    assumption/InfoExternal(cname=c) -> c
    _ -> name

fun cname(info: nameInfo)
  match info
    InfoVal(cname=c) -> c
    InfoFun(cname=c) -> c
    assumption/InfoExternal(cname=c) -> c
    _ -> throw("type/assumption cname")

fun is-info-val-fun-ext(info)
  match info
    InfoVal() -> True
    InfoFun() -> True
    assumption/InfoExternal() -> True
    _ -> False

fun is-info-fun-or-external(info)
  match info
    InfoFun() -> True
    assumption/InfoExternal() -> True
    _ -> False

fun doc(info)
  match info
    InfoVal(doc=d) -> d
    InfoFun(doc=d) -> d
    InfoCon(doc=d) -> d
    assumption/InfoExternal(doc=d) -> d
    _ -> ""

fun fipT(info: nameInfo)
  match info
    InfoFun(fipt=fipt) -> fipt
    assumption/InfoExternal(fipt=fipt) -> fipt
    _ -> no-fip

fun element(info: nameInfo)
  match info
    InfoCon() -> "constructor"
    InfoImport() -> "import"
    _ -> "identifier"

fun is-visible(info: nameInfo)
  info.vis.is-public

fun core-var-info(info: nameInfo)
  match info
    InfoVal -> InfoNone
    InfoFun(arity=(m,n)) -> InfoArity(m, n)
    assumption/InfoExternal(format=f) -> compiler/core/core/InfoExternal(f)

fun core-expr(info: nameInfo, qname: name)
  match info
    InfoVal(_, cname, tp) -> Var(TName(cname, tp), InfoNone)
    InfoFun(_, cname, tp, (m, n), _) -> Var(TName(cname, tp), InfoArity(m ,n))
    InfoCon(_, tp, repr) -> Con(TName(qname, tp), repr)
    assumption/InfoExternal(_, cname, tp, format) -> Var(TName(cname, tp), compiler/core/core/InfoExternal(format))

// Names to type schemes.
// Due to overloading there may be multiple entries for the same qualified name

alias gamma = name-map<list<(name, nameInfo)>>
val empty:gamma = LinearMap([])

fun schemes(g: gamma): list<scheme>
  g.gamma-list.map(fn(n) n.snd.typ)

fun single(name: name, ni: nameInfo)
  assumption/empty.set(name, [(name, ni)])

fun gamma-extends(g: gamma, ls: list<(name,nameInfo)>): gamma
  ls.foldl(g, fn(m, (name,tp)) m.gamma-extend(name, tp))

fun gamma-extend(g: gamma, name: name, ni: nameInfo)
  g.update(name.unqualify-full, [(name, ni)], fn(old, new) old ++ new) // TODO: Check for overlapping type schemes?

fun gamma-lookup-canonical(g: gamma, name: name)
  g.gamma-lookupQ(name).filter(fn(ni) ni.canonical-name(nil) == name)

fun gamma-lookup-exact-con(g: gamma, name: name)
  g.gamma-lookupQ(name).filter(is-infoCon)

// Return exactly matching qualified names
fun gamma-lookupQ(g: gamma, name: name)
  match g.lookup(name.unqualify-full)
    Nothing -> []
    Just(xs) -> xs.filter(fn(n) n.fst == name).map(snd)

// @gamma-lookup name gamma@ looks up a potentially (partially) qualified name and returns all matches.
fun gamma-lookup(g: gamma, name: name)
  val stem-name = name.unqualify-full
  match g.lookup(stem-name)
    Nothing -> []
    Just(candidates0) ->
      val candidates1 = candidates0.filter(fn((_, i)) i.is-visible)
      if stem-name == name then candidates1 // Fast path for unqualified names
      else
        val qpaths = name.split-rev-qualifiers
        candidates1.filter(fn((n,_)) match-rev-qualifier-paths(qpaths, n.split-rev-qualifiers))

// Given a user qualified name, see if the qualifiers match a resolved name.
// The user qualified name has already been de-aliased in kind inference (see `Kind/ImportMap/importsExpand`)
// Note that the user qualified name might not distinguish local qualification from module qualification,
// e.g. `std/core/int/show` vs  `std/core/#int/show`.
// ambiguities may occur, where `std/num/float32/foo` should match both `std/num/#float32/foo` and `std/num/float32/#foo`
fun match-qualifiers(uname: name, name: name)
  match-rev-qualifier-paths(uname.split-rev-qualifiers, name.split-rev-qualifiers)

fun is-prefix-of(u: list<string>, p: list<string>)
  u.length <= p.length && u.zip(p).all(fn((a, b)) a == b)

fun match-rev-qualifier-paths(upaths: (list<string>,list<string>), paths: (list<string>,list<string>)): bool
  match (upaths, paths)
    (([], []), (Cons, Cons)) -> True // not qualified
    ((umpath, []), (mpath, [])) -> umpath.is-prefix-of(mpath) // no user specified local path
    ((umpath, []), (mpath, lpath)) -> // not (null lpath)
      umpath.is-prefix-of(lpath) || // user module is a postfix the local qualifier
      lpath.is-prefix-of(umpath) && umpath.drop(lpath.length).is-prefix-of(mpath) || // stradle both
      umpath.is-prefix-of(mpath) // user module is postfix of the module qualifier (we can not mention local qualfiiers, so `std/core/show` matches `std/core/#int/show` for example)
    ((umpath, ulpath), (mpath, lpath)) -> // not (null ulpath)
      match umpath
        [] -> ulpath.is-prefix-of(lpath)
        _ -> ulpath == lpath && umpath.is-prefix-of(mpath)

// Split out the module and local qualifier as a _reverse_ list of components
// e.g. `std/core/#int/show` -> (["core","std"],["int"])
fun split-rev-qualifiers(name: name): (list<string>, list<string>)
  val mpath = name.split-module-name.reverse
  val lpath = name.split-local-qual-name.reverse
  (mpath, lpath)

fun gamma-lookup-prefix(g: gamma, name: name): list<(name, nameInfo)>
  val pre = name.unqualify.show-plain ++ "_"
  fun is-prefix(nm: name)
    nm == name || nm.name/name/starts-with(pre)
  g.filter(fn(n, ni) n.is-prefix).values.concat.filter(fn((_, ni)) ni.is-visible)

fun gamma-map(g: gamma, f: (nameInfo -> nameInfo)): gamma
  g.map(fn(k, xs) (k, xs.map(fn((n, ni)) (n, f(ni)))))

fun gamma-list(g: gamma): list<(name, nameInfo)>
  g.list.map(snd).concat.sort-by(fn((n, _), (n2, _)) n.name/name/cmp(n2))

fun gamma-remove(g: gamma, name: name)
  g.remove(name.unqualify)

fun gamma-union(g1: gamma, g2: gamma)
  g2.union-with(g1, fn(xs1, xs2) xs1 ++ xs2)

fun gamma-unions(gs: list<gamma>)
  gs.foldl(compiler/type/assumption/empty, gamma-union)

// Filter out signature belonging to a module
fun gamma-filter(g: gamma, mod: name)
  g.filter(fn(k, _) k.qualifier == mod)

fun gamma-names(g: gamma)
  g.keys

fun gamma-public-names(g: gamma)
  g.filter(fn(n, nis) !n.is-hidden-name && nis.all(fn((_, ni)) ni.is-visible)).keys

// Extract from core
fun extract-gamma-imports(imports: list<(name,name)>, modName: name): gamma
  val modAlias = modName //.nameStem.list.reverse.take-while(fn(a) a != '.').reverse.string.new-name
  imports.map(extract-import).gamma-unions.gamma-extend(modAlias, InfoImport(Private, typeVoid, modAlias, modName, null))

fun extract-import((name, qname))
  qname-map/single(name, InfoImport(Private, typeVoid, name, qname, null))

// Extract a Gamma from a Core module
fun extract-gamma(isValue: (dataInfo -> bool), privateAsPublic: bool, c: core): <exn, comp-flags> gamma
  fun update-vis(vis)
    match vis
      Public -> Public
      _ -> if privateAsPublic then Public else vis
  gamma-unions([
    c.defs.map(fn(dg) dg.extract-def-group(update-vis)).gamma-unions,
    c.externals.map(fn(ex) ex.extract-external(update-vis)).gamma-unions,
    c.typeDefs.map(fn(td) td.extract-type-def-group(isValue, update-vis)).gamma-unions
  ])

fun extract-type-def-group(td: typeDefGroup, isValue: (dataInfo -> bool), update-vis)
  td.map(fn(d) extract-type-def(isValue, update-vis, d)).gamma-unions

fun extract-type-def(isValue: (dataInfo -> bool), update-vis, td: typeDef)
  fun extract-con-info((info, repr): (conInfo, conRepr))
    qname-map/single(info.name, InfoCon(update-vis(info.vis), info.typeScheme, repr, info, info.range, info.doc))
  match td
    Data(dataInfo, _) -> zip(dataInfo.constrs, dataInfo.dataRepr(isValue).snd).map(extract-con-info).gamma-unions
    _ -> assumption/empty

fun extract-def-group(d: defGroup, update-vis)
  match d
    DefRec(defs) -> defs.map(fn(v) extract-def(v, update-vis)).gamma-unions
    DefNonRec(v) -> extract-def(v, update-vis)

fun extract-def(d: def, update-vis)
  qname-map/single(d.def-name, create-name-infoX(update-vis(d.vis), d.def-name, d.sort, d.nameRange, d.ktype, d.doc)) // specials since we cannot call isTopLevel as in coreDefInfo

fun core-def-info(d: def)
  (d.def-name, create-name-infoX(d.vis, d.def-name, if d.sort.is-defFun && !d.is-top-level then DefVal else d.sort, d.nameRange, d.ktype, d.doc))
// since we use coreDefInfo also for local definitions, we need to be careful to to use DefFun for
// things that do not get lifted to toplevel due to free type/variables. test: codegen/rec5

fun create-name-infoX(vis, name, sort, rng, tp, doc)
  match sort
    DefFun(_, fipT) -> InfoFun(vis, name, tp, tp.arity, fipT, rng, doc)
    DefVar -> InfoVal(vis, name, tp, rng, True, doc)
    _ -> InfoVal(vis, name, tp, rng, False, doc)

fun arity(tp: ktype): <comp-flags, exn> (int, int)
  match tp.expandSyn
    TForAll(tvars, _, t) ->
      match t.expandSyn
        TFun(pars) -> (tvars.length, pars.length)
        _ -> (tvars.length, -1)
    TFun(pars) -> (0, pars.length)

fun extract-external(external: external, update-vis)
  match external
    External(name, tp, _, body, vis, fipT, nameRng, doc) ->
      qname-map/single(name, InfoExternal(update-vis(vis), name, tp, body, fipT, nameRng, doc))
    _ -> assumption/empty

// TODO: ftc
// Instances

fun gamma/(|->)(sub: sub, g: gamma): pure gamma
  g.map(fn(n, nis) (n, nis.map(fn((n1, ni)) (n1, sub |-> ni))))

fun gamma/free-type-vars(g: gamma): pure tvs
  g.schemes.map(free-type-vars).unions

fun gamma/bound-type-vars(g: gamma): pure tvs
  g.schemes.map(scheme/bound-type-vars).unions

fun ni/(|->)(sub: sub, ni: nameInfo): pure nameInfo
  ni.map-type(fn(t) sub |-> t)

fun ni/free-type-vars(info: nameInfo): pure tvs
  info.typ.free-type-vars

fun ni/bound-type-vars(info: nameInfo): pure tvs
  info.typ.bound-type-vars

fun map-type(ni: nameInfo, f: (ktype) -> e ktype): e nameInfo
  match ni
    InfoVal(vis, cname, typ, range, isVar) -> InfoVal(vis, cname, f(typ), range, isVar)
    InfoFun(vis, cname, typ, arity, fipt, range) -> InfoFun(vis, cname, f(typ), arity, fipt, range)
    InfoCon(vis, typ, repr, conInfo, range) -> InfoCon(vis, f(typ), repr, conInfo, range)
    assumption/InfoExternal(vis, cname, typ, format, fipt, range) -> assumption/InfoExternal(vis, cname, f(typ), format, fipt, range)
    InfoImport(vis, typ, nameAlias, fullName, range) -> InfoImport(vis, f(typ), nameAlias, fullName, range)

fun pp-gamma-internal(g: gamma, showHidden: bool)
  val nameSchemes = g.gammaList.map(fn((n, i)) (n, i.typ))
  val maxWidth = nameSchemes.map(fn((n, _)) n.show.count).maximum(0).min(12)
  fun nice(scheme: ktype)
    align(niceTypes([scheme]).head.unjust)
  vcat(nameSchemes.filter(fn((n, _)) showHidden || !n.is-hidden-name).map(fn((n, s))
    fill(n.show-plain.text |.| typeColon().color(colors.colorSep) |+| align(nice(s)), maxWidth)
  ))

fun pp-gamma(g: gamma)
  pp-gamma-internal(g, False)

fun pp-gamma-hidden(g: gamma)
  pp-gamma-internal(g, True)

fun pretty(g: gamma): <ppTypeEff> doc
  pp-gamma(g)

fun show-gamma(g: gamma): ppTypeEff string
  pretty(g).show
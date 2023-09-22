import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/type/type
import compiler/core/core
import compiler/common/name-collections
import newstd/data/linearmap
import newstd/data/sort

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
    InfoVal(vis, cname, typ, range, isVar) -> "InfoVal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ showFullRange(range) ++ ", " ++ show(isVar) ++ ")"
    InfoFun(vis, cname, typ, arity, fipt, range) -> "InfoFun(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-tuple(arity, show, show) ++ ", " ++ show(fipt) ++ ", " ++ showFullRange(range) ++ ")"
    InfoCon(vis, typ, repr, conInfo, range) -> "InfoCon(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(repr) ++ ", " ++ show(conInfo) ++ ", " ++ showFullRange(range) ++ ")"
    assumption/InfoExternal(vis, cname, typ, format, fipt, range) -> "InfoExternal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show-list(format, fn(s) s.show-tuple(show, fn(x) x)) ++ ", " ++ show(fipt) ++ ", " ++ showFullRange(range) ++ ")"
    InfoImport(vis, typ, nameAlias, fullName, range) -> "InfoImport(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(nameAlias) ++ ", " ++ show(fullName) ++ ", " ++ showFullRange(range) ++ ")"

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

fun coreExpr(qname: name, info: nameInfo)
  match info
    InfoVal(_, cname, tp) -> Var(TName(cname, tp), InfoNone)
    InfoFun(_, cname, tp, (m, n), _) -> Var(TName(cname, tp), InfoArity(m ,n))
    InfoCon(_, tp, repr) -> Con(TName(qname, tp), repr)
    assumption/InfoExternal(_, cname, tp, format) -> Var(TName(cname, tp), compiler/core/core/InfoExternal(format))
    _ -> throw("type/assumption coreExpr")

// Names to type schemes.
// Due to overloading there may be multiple entries for the same qualified name

alias gamma = name-map<list<(name, nameInfo)>>
val nameEq = fn(n1: name, n2: name) n1 == n2
val listEq = fn(l1: list<(name, nameInfo)>, l2: list<(name, nameInfo)>) (==)(l1, l2, fn((n1, ni1), (n2, ni2)) n1 == n2 && ni1 == ni2)
val showList = fn(l: list<(name, nameInfo)>) show-list(l, fn((n, ni)) show(n) ++ " -> " ++ show(ni))
val empty = linearMap([], nameEq, listEq, show, showList)

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

// TODO: Union with 
import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/type/type
import compiler/core/core
import compiler/common/name-collections

type nameInfo
  InfoVal(vis: visibility, cname: name, typ: scheme, range: range, isVar: bool)
  InfoFun(vis: visibility, cname: name, typ: scheme, arity: (int, int), fipt: fipT, range: range)
  InfoCon(vis: visibility, typ: scheme, repr: conRepr, conInfo: conInfo, range: range)
  InfoExternal(vis: visibility, cname: name, typ: scheme, format: list<(target, string)>, fipt: fipT, range: range)
  InfoImport(vis: visibility, typ: scheme, nameAlias: name, fullName: name, range: range)

fun (==)(ni1: nameInfo, ni2: nameInfo)
  match (ni1, ni2)
    (InfoVal(vis, cname, typ, range, isVar), InfoVal(vis2, cname2, typ2, range2, isVar2)) -> vis == vis2 && cname == cname2 && typ == typ2 && range == range2 && isVar == isVar2

fun canonicalName(name: name, info: nameInfo)
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
val empty = linearMap([], nameEq, listEq, show, show)
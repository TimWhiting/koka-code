import compiler/common/failure
import compiler/lib/pprint
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/type/type
import compiler/kind/kind
import compiler/type/typevar
import compiler/type/pretty
import newstd/data/sort
import newstd/data/linearset

alias range-map = list<(range, rangeInfo)>

fun mangleConName(nm: name)
  prepend("con", nm)

fun mangleTypeName(nm: name)
  prepend("type", nm)

fun mange(nm: name, tp: ktype)
  nm

type rangeInfo
  RIDecl(kind: string, name: name, name2: name) // alias, type, cotype, rectype, fun, val
  RIBlock(str: string) // type, kind, pattern
  RIError(d: doc)
  RIWarning(d: doc)
  RIId(name: name, ninfo: nameInfo, isDefinition: bool) // qualified name, info, is the definition

value type nameInfo
  NIValue(tp: ktype)
  NICon(tp: ktype)
  NITypeCon(k: kind)
  NITypeVar(k: kind)
  NIModule
  NIKind

fun show(ri: rangeInfo): string
  match ri
    RIDecl(kind, name, name2) -> "Decl " ++ kind ++ " " ++ show(name) ++ " " ++ show(name2)
    RIBlock(str) -> "Block " ++ str
    RIError -> "Error"
    RIWarning -> "Warning"
    RIId(name, _, isDefinition) -> "Id " ++ show(name) ++ (if isDefinition then " (def)" else "")

fun int(ri: rangeInfo)
  match ri
    RIDecl -> 0
    RIBlock -> 10
    RIId -> 20
    RIWarning -> 30
    RIError -> 40

fun penalty(nm: name)
  if nm.nameModule == "std/core/hnd" then 10 else 0

fun int(ni: nameInfo)
  match ni
    NIValue -> 1
    NICon -> 2
    NITypeCon -> 3
    NITypeVar -> 4
    NIModule -> 5
    NIKind -> 6

fun isHidden(ri: rangeInfo)
  match ri
    RIDecl(_, nm1) -> nm1.isHiddenName
    RIId(nm) -> nm.isHiddenName
    _ -> False

val rangeMapNew:range-map = []

fun cut(r: range)
  Range(r.start, r.start)

fun insert(rm: range-map, r: range, ri: rangeInfo)
  if ri.isHidden then rm
  else
    val beginEndToken =
      match ri
        RIId(nm) -> nm == nameUnit || nm == nameNull || nm.isNameTuple
        _ -> False
    if beginEndToken then Cons((r, ri), Cons((Range(r.end,r.end), ri), rm))
    else Cons((r, ri), rm)

fun append(rm1: range-map, rm2: range-map)
  rm1 ++rm2

fun sort(rm: range-map)
  rm.sortBy(fn((r1, _), (r2, _)) r1.compare(r2))

fun lookup(rm: range-map, r: range)
  val pos = r.start
  fun isBefore((rng, _)) rng.start < pos
  fun startsAt((rng, _)) rng.start == pos
  val (rinfos, rm') = rm.drop-while(isBefore).span(startsAt)
  fun cmp((_, ri1: rangeInfo), (_, ri2: rangeInfo)) ri1.int.compare(ri2.int)
  fun eq((_, ri1: rangeInfo), (_, ri2: rangeInfo)) ri1.int / 10 == ri2.int / 10
  val prioritized = rinfos.sortBy(cmp).groupBy(eq)
  (prioritized, rm')

fun findAt(rm: range-map, p: pos)
  fun containsPos(r: range)
    r.start <= p && p <= r.end
  fun shortestRange(rm': range-map)
    match rm'
      Cons((r1, ri1), Cons((r2, ri2), rst)) -> 
        if r1.length < r2.length then shortestRange(Cons((r1, ri1),rst)) 
        else shortestRange(Cons((r2, ri2),rst))
      Cons(r, Nil) -> Just(r)
      Nil -> Nothing
  rm.filter(fn(r) r.fst.containsPos).shortestRange

fun riType(ri: rangeInfo)
  match ri
    RIId(_, i) ->
      match i
        NIValue(tp) -> Just(tp)
        NICon(tp) -> Just(tp)
        _ -> Nothing
    _ -> Nothing

fun (|->)(s: sub, rm: range-map): pure range-map
  rm.map(fn((r, ri)) (r, s |-> ri))

fun freeTypeVars(rm: range-map): pure tvs
  rm.map(snd).map(freeTypeVars).unions

fun boundTypeVars(rm: range-map): pure tvs
  rm.map(snd).map(boundTypeVars).unions

fun (|->)(s: sub, ri: rangeInfo): pure rangeInfo
  match ri
    RIId(nm, i, isDef) -> RIId(nm, s |-> i, isDef)
    _ -> ri

fun (|->)(s: sub, ni: nameInfo): pure nameInfo
  match ni
    NIValue(tp) -> NIValue(s |-> tp)
    NICon(tp) -> NICon(s |-> tp)
    _ -> ni

fun freeTypeVars(ri: rangeInfo): pure tvs
  match ri
    RIId(_, i) -> freeTypeVars(i)
    _ -> emptyTvs

fun boundTypeVars(ri: rangeInfo): pure tvs
  match ri
    RIId(_, i) -> boundTypeVars(i)
    _ -> emptyTvs

fun freeTypeVars(ni: nameInfo): pure tvs
  match ni
    NIValue(tp) -> freeTypeVars(tp)
    NICon(tp) -> freeTypeVars(tp)
    _ -> emptyTvs

fun boundTypeVars(ni: nameInfo): pure tvs
  match ni
    NIValue(tp) -> boundTypeVars(tp)
    NICon(tp) -> boundTypeVars(tp)
    _ -> emptyTvs
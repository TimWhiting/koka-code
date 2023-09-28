import compiler/core/core
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import newstd/data/linearmap

alias inlines = name-map<inlineDef>

val inlinesEmpty = linearMap([], nameEq, fn(inl1: inlineDef, inl2: inlineDef) inl1 == inl2, show, show)

fun inlinesNew(xs: list<inlineDef>)
  inlinesEmpty.extends(xs)

fun extends(inls: inlines, xs: list<inlineDef>)
  xs.foldl(inls, extend)

fun extend(inls: inlines, inl: inlineDef)
  inls.add(inl.defName, inl)

fun merge(inls1: inlines, inls2: inlines)
  inls1.union(inls2)

fun extractInlineDefs(costMax: int, dgs: defGroups)
  dgs.map(fn(dg) dg.extractDefGroup(costMax)).concat

fun extractDefGroup(dg: defGroup, costMax: int)
  match dg
    DefRec() -> []
    DefNonRec(d) -> d.extractInlineDef(costMax, False).map(fn(d') [d']).default([])

fun extractInlineDef(d: def, costMax: int, isRec: bool)
  val inlineable = d.isInlineable(costMax)
  if !inlineable then Nothing
  else
    val cost = (if d.defName == nameBind || d.defName == nameBind2 then 0 else d.cost)
    Just(InlineDef(d.defName, d.defExpr, isRec, d.kinline, cost, d.sort, []))
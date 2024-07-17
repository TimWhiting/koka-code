import compiler/core/core
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import std/data/linearmap

alias inlines = name-map<inlineDef>

val empty:inlines = LinearMap([])

fun inlines(xs: list<inlineDef>)
  empty.extends(xs)

fun extends(inls: inlines, xs: list<inlineDef>)
  xs.foldl(inls, extend)

fun extend(inls: inlines, inl: inlineDef)
  inls.add(inl.def-name, inl)

fun merge(inls1: inlines, inls2: inlines)
  inls1.union(inls2)

fun defs/extract-inlines(dgs: defGroups, costMax: int)
  dgs.map(fn(dg) dg.extract-inlines(costMax)).concat

fun dg/extract-inlines(dg: defGroup, costMax: int)
  match dg
    DefRec() -> []
    DefNonRec(d) -> d.extract-inlines(costMax, False).map(fn(d') [d']).default([])

fun def/extract-inlines(d: def, costMax: int, isRec: bool)
  val inlineable = d.isInlineable(costMax)
  if !inlineable then Nothing
  else
    val cost = (if d.def-name == nameBind || d.def-name == nameBind2 then 0 else d.cost)
    Just(InlineDef(d.def-name, d.defExpr, isRec, d.kinline, cost, d.sort, []))
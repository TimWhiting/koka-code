import compiler/common/name
import compiler/core/core
import compiler/common/failure
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-collections
import compiler/common/range
import std/data/linearmap

// Map names to their borrowing info. If a name does not use borrowing
// it may not be in here.
alias borrowed = name-map<list<paramInfo>>

alias borrowDef = (name, list<paramInfo>)

// The initial borrowed
val empty:borrowed = LinearMap([])

fun borrowedNew(xs: list<borrowDef>): borrowed
  borrowed/empty.extend(xs)

fun list/extend(b: borrowed, xs: list<borrowDef>): borrowed
  xs.foldl(b, extend)

fun borrowed/extend(b: borrowed, b1: borrowDef): borrowed
  b.add(b1.fst, b1.snd)

fun core/extend(c: core, b0: borrowed): borrowed
  b0.extend(c.defs.extract-borrow).extend(c.externals.extract-borrow)

// Get borrow information from core
fun dgs/extract-borrow(dgs: defGroups)
  dgs.map(extract-borrow).concat

fun externs/extract-borrow(exs: externals)
  exs.map(extract-borrow).concat-maybe

fun ext/extract-borrow(ex: external)
  match ex
    External(nm, _, params) ->
      if params.any(fn(p) p == Borrow) then Just((nm, params)) else Nothing
    _ -> Nothing

fun dg/extract-borrow(dg: defGroup)
  match dg
    DefRec(defs) -> defs.map(fn(d) d.extract-borrow(True)).concat-maybe
    DefNonRec(d) -> d.extract-borrow(False).map(fn(d') [d']).default([])

fun def/extract-borrow(d: def, rec: bool)
  match d.sort
    DefFun(pinfos) | !pinfos.is-nil -> Just((d.def-name, pinfos))
    _ -> Nothing
    


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
val borrowedEmpty = []

fun borrowedNew(xs: list<borrowDef>): borrowed
  borrowedEmpty.extends(xs)

fun extends(b: borrowed, xs: list<borrowDef>): borrowed
  xs.foldl(b, extend)

fun extend(b: borrowed, b1: borrowDef): borrowed
  b.add(b1.fst, b1.snd)

fun extendICore(c: core, b0: borrowed): borrowed
  b0.extends(c.defs.extractBorrowDefs).extends(c.externals.extractBorrowExternals)

// Get borrow information from core
fun extractBorrowDefs(dgs: defGroups)
  dgs.map(extractDefGroup).concat

fun extractBorrowExternals(exs: externals)
  exs.map(extractExternal).concat-maybe

fun extractExternal(ex: external)
  match ex
    External(nm, _, params) ->
      if params.any(fn(p) p == Borrow) then Just((nm, params)) else Nothing
    _ -> Nothing

fun extractDefGroup(dg: defGroup)
  match dg
    DefRec(defs) -> defs.map(fn(d) d.extractBorrowDef(True)).concat-maybe
    DefNonRec(d) -> d.extractBorrowDef(False).map(fn(d') [d']).default([])

fun extractBorrowDef(d: def, rec: bool)
  match d.sort
    DefFun(pinfos) | !pinfos.is-nil -> Just((d.def-name, pinfos))
    _ -> Nothing
    


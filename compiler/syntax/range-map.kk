//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 8/6/24: Commit 7d99cb0

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
import compiler/syntax/lexeme
import std/data/linearset
import newstd/data/sort

pub infixr 5 (|->)

alias range-map = list<(range, rangeInfo)>

fun rm-find-first(rm: range-map, p: (rangeInfo) -> e bool): e maybe<(range, rangeInfo)>
  match rm.filter(fn((_,ri)) p(ri))
    Nil -> Nothing
    Cons(x, _) -> Just(x)

fun rm-find-all(rm: range-map, p: (rangeInfo) -> e bool): e list<(range, rangeInfo)>
  rm.filter(fn((_,ri)) p(ri))

fun mangle-con-name(nm: name)
  prepend("con", nm)

fun mangle-type-name(nm: name)
  prepend("type", nm)

fun mangle(nm: name, tp: ktype)
  nm

type rangeInfo
  RIDecl(kind: string, name: name, name2: name, tp: maybe<ktype>) // alias, type, cotype, rectype, fun, val
  RIBlock(str: string) // type, kind, pattern
  RIError(d: doc)
  RIWarning(d: doc)
  RIId(name: name, ninfo: nameInfo, docs: list<doc>, isDefinition: bool) // qualified name, info, extra doc (from implicits), is this the definition?
  RIImplicits(shorten: (bool) -> doc) // inferred implicit arguments and (implicit) resume arguments

type nameInfo
  NIValue(sort: string, tp: ktype, comment: string, isAnnotated: bool) // sort is fun, val, etc.
  NICon(tp: ktype, comment: string)
  NITypeCon(k: kind, comment: string)
  NITypeVar(k: kind)
  NIModule
  NIKind

fun ni/show(ni: nameInfo): <comp-flags,pure> string
  match ni
    NITypeCon(_, d) -> "TypeCon: " ++ d
    NIValue(srt, tp, d) -> "Value " ++ srt ++ ": " ++ tp.pretty.show ++ ": " ++ d
    NICon(tp, d) -> "Con : " ++ tp.pretty.show ++ ": " ++ d
    NITypeVar -> "TypeVar"
    NIModule -> "Module"
    NIKind -> "Kind"

fun ri/show(ri: rangeInfo): <comp-flags,pure> string
  match ri
    RIDecl(kind, name, name2, mbtp) -> 
      "Decl " ++ kind ++ " " ++ show(name) ++ " " ++ show(name2) ++ mbtp.map(fn(tp) ": " ++ tp.pretty.show).default("")
    RIBlock(str) -> "Block " ++ str
    RIError -> "Error"
    RIWarning -> "Warning"
    RIId(name, info, docs, isDefinition) -> 
      "Id " ++ show(name) ++ (if isDefinition then " (def)" else "") ++ docs.show ++ ", info: " ++ info.show
    RIImplicits(shorten) -> "Implicits " ++ shorten(False).show

fun ri/int(ri: rangeInfo)
  match ri
    RIDecl -> 0
    RIBlock -> 10
    RIId -> 20
    RIImplicits -> 25
    RIWarning -> 40
    RIError -> 50

fun penalty(nm: name)
  if nm.nameModule == "std/core/hnd" then 10 else 0

fun ni/int(ni: nameInfo)
  match ni
    NIValue -> 1
    NICon -> 2
    NITypeCon -> 3
    NITypeVar -> 4
    NIModule -> 5
    NIKind -> 6

fun is-hidden(ri: rangeInfo)
  match ri
    RIDecl(_, nm) -> nm.is-hidden-name
    RIId(nm) -> nm.is-hidden-name
    _ -> False

val new/range-map:range-map = []

fun cut(r: range)
  Range(r.start, r.start, r.hidden)

fun insert(rm: range-map, r: range, ri: rangeInfo)
  if ri.is-hidden || r.is-null || r.hidden then rm
  else
    val begin-end-token =
      match ri
        RIId(nm) -> nm == nameUnit || nm == nameNull || nm.is-name-tuple
        _ -> False
    if begin-end-token then Cons((r, ri), Cons((Range(r.end,r.end,r.hidden), ri), rm))
    else Cons((r, ri), rm)

fun append(rm1: range-map, rm2: range-map)
  rm1 ++ rm2

fun sort(rm: range-map)
  rm.sort-by(?cmp = fn((r1, _), (r2, _)) r1.cmp(r2))

// select the best matching range infos from a selection
fun prioritize(rm: range-map)
  fun this-cmp((_, ri1: rangeInfo), (_, ri2: rangeInfo)) ri1.int.cmp(ri2.int)
  fun eq((_, ri1: rangeInfo), (_, ri2: rangeInfo)) ri1.int / 10 == ri2.int / 10
  val sorted = rm.filter(fn((_, ri)) !ri.is-rIimplicits).sort-by(?cmp=this-cmp)
  // Merge implicit documentation into identifiers
  val idocs = 
        rm.map fn((_, rinfo))
          match rinfo
            RIImplicits(fdoc) -> [fdoc(False)] // Do not shorten for hover info
            _ -> []
  val idocsrev = idocs.concat.reverse
  // merge implicit documentation into identifiers
  fun merge-docs((rng, ri))
    match ri
      RIId(name, info, docs, isDef) -> (rng, RIId(name, info, docs ++ idocsrev, isDef))
      _ -> (rng, ri)
  sorted.group-by(eq).map(fn(rs) rs.last.unjust.merge-docs())

fun merge-implicits(rm: range-map, for-inlay: bool)
  val idocs = 
        rm.map fn((rng, rinfo))
          match rinfo
            RIImplicits(fdoc) -> [(rng, fdoc(for-inlay))]
            _ -> []
  val idocsc = idocs.concat
  fun find-docs(r: range)
    idocsc.filter(fn((rng, _)) r == rng).map(snd).reverse
  fun merge(rinfos0)
    match rinfos0
      Nil -> Nil
      Cons((rng, rinfo), rinfos) ->
        match rinfo
          RIImplicits -> merge(rinfos)
          RIId(nm, info, docs, isDef) -> Cons((rng, RIId(nm, info, (if for-inlay then [] else docs) ++ find-docs(rng), isDef)), merge(rinfos))
          _ -> Cons((rng, rinfo), merge(rinfos))
  merge(rm)

fun lookup(rm: range-map, r: range)  
  val pos = r.start
  fun is-before((rng, _)) rng.start < pos
  fun starts-at((rng, _)) rng.start == pos
  val (rinfos, rm') = rm.drop-while(is-before).span(starts-at)
  (rinfos.prioritize, rm')

fun find-in(rm: range-map, r: range, for-inlay: bool): list<(range, rangeInfo)>
  val s = r.start
  val e = r.end
  val res = rm.filter fn((ri, _))
              ri.start >= s || ri.end <= e
  res.merge-implicits(for-inlay)

// Gets all lexemes less than the given position and then reverses their order
fun previous-lexemes-reversed(lexes: list<lexeme>, p: pos)
  lexes.take-while(fn(l) l.range.start < p).reverse

// Drops everything inside and including matched parentheses, assumes the ending paren is already dropped
fun drop-matched-parens-reverse(lexes: list<lexeme>)
  lexes.drop-to-lex-matching(fn(l) l == LexSpecial(")"), fn(l) l == LexSpecial("("))

// Assumes in the middle of the function parameters
// (drops to nearest open paren that didn't have a close paren before it)
// This takes care of finding signature info when a cursor is in an argument list
fun get-function-incomplete-reverse(lexes: list<lexeme>)
  lexes.drop-auto-gen-closing.drop-matched-parens-reverse.get-function-name-reverse

// Assumes it is given reverse ordered lexemes ending at an end of a function invocation
// 
// e.g.
//   a.b(x, y, fn() {z}).abc
//   => FnChained "b" "abc" -- had a .abc after the b
// also
//   a.b
//   => FnNormal "a"
// and
//   a.
//   => FnNormal "a"
// and finally
//   (abc).abc => NotFound
fun get-function-name-reverse(xs0: list<lexeme>)
  fun go(xs: list<lexeme>)
    match xs
      [] -> EmptyStatement
      // "" 10 1.0 'c' [] x etc... (literals, identifiers that can have a function call via . after them)
      Cons(v as Lexeme(_, LexString)) -> FnValue(v)
      Cons(v as Lexeme(_, LexInt)) -> FnValue(v)
      Cons(v as Lexeme(_, LexFloat)) -> FnValue(v)
      Cons(v as Lexeme(_, LexChar)) -> FnValue(v)
      Cons(v as Lexeme(_, LexSpecial("]"))) -> FnValue(v)
      Cons(v as Lexeme(_, LexId)) -> FnValue(v)
      // x(). or (x.y). or even (1 + 2). -- The last will return a chain in FnNotFound
      Cons(Lexeme(_, LexKeyword(".")), xs') -> FnIncomplete(xs'.go)
      // x() or (x.y) or even (1 + 2) -- The last will return FnNotFound
      Cons(Lexeme(_, LexSpecial(")")), xs') -> 
        val dropped = xs.drop-matched-parens-reverse
        match dropped.go
          // (a).b -- if there is nothing before the parenthesized expression
          // it doesn't mean there isn't a chained function target
          EmptyStatement -> xs'.go
          res -> res
      // x.partial, x().partial etc
      Cons(f as Lexeme(_, LexId), Lexeme(_, LexKeyword(".")), xs') ->
        chain(f, xs'.go)
      _ -> FnNotFound(xs)
  xs0.drop-auto-gen-closing.get-current-statement-reverse.go

// Add a function to a chain of discovered functions
fun chain(fn0: lexeme, chain: fn-syntax)
  match chain
    FnChained -> FnChained(fn0, chain)
    FnValue -> FnChained(fn0, chain)
    FnIncomplete(ch) -> FnChained(fn0, ch)
    EmptyStatement -> FnValue(fn0)
    FnNotFound(fxs) -> FnValue(fn0)

type fn-syntax
  FnChained(name: lexeme, chain: fn-syntax) // a.b.c -- The chain's return type is the function's first argument type
  FnIncomplete(chain: fn-syntax) // a.b. -- imcomplete . 
  FnValue(value: lexeme) // a / ] / 10 / "abc" / etc. -- The object of a function call (a literal or identifier)
  FnNotFound(fprefix: list<lexeme>)
  EmptyStatement // start of line

fun fnsyntax/show(f: fn-syntax)
  match f
    FnChained(fx, chain) -> fx.show ++ "." ++ chain.show
    FnIncomplete(ch) -> ch.show ++ "."
    FnValue(fx) -> fx.show
    FnNotFound(fxs) -> fxs.length.show ++ ":" ++ fxs.take(6).show
    EmptyStatement -> "EmptyStatement"

// Assumes reverse ordered lexemes
// Gets the current statement (e.g. up to the last ; or implicit ;, accounting for nesting, and blocks)
// Ignores statements within nested blocks
fun get-current-statement-reverse(xs0: list<lexeme>)
  fun go(xs: list<lexeme>, blockn: int)
    match xs
      [] -> []
      Cons(Lexeme(_, LexSpecial(";")), xs) | blockn == 0 -> []
      Cons(Lexeme(_, LexInsSemi), xs) | blockn == 0 -> []
      Cons(x as Lexeme(_, LexSpecial("}")), xs) -> Cons(x, go(xs, blockn + 1))
      Cons(x as Lexeme(_, LexInsRCurly), xs) -> Cons(x, go(xs, blockn + 1))
      Cons(x as Lexeme(_, LexSpecial("{")), xs) -> Cons(x, go(xs, blockn - 1))
      Cons(x as Lexeme(_, LexInsLCurly), xs) -> Cons(x, go(xs, blockn - 1))
      Cons(x, xs) -> Cons(x, go(xs, blockn))
  go(xs0, 0)


// Gets the current block of syntax (e.g. up to the last { or implicit {, accounting for nesting)
fun get-current-block-reverse(xs0: list<lexeme>)
  fun go(xs: list<lexeme>, n: int)
    match xs
      [] -> []
      Cons(Lexeme(_, LexSpecial("{")), xs) | n == 0 -> []
      Cons(Lexeme(_, LexInsLCurly), xs) | n == 0 -> []
      Cons(x as Lexeme(_, LexSpecial("}")), xs) -> Cons(x, go(xs, n + 1))
      Cons(x as Lexeme(_, LexInsRCurly), xs) -> Cons(x, go(xs, n + 1))
      Cons(x as Lexeme(_, LexSpecial("{")), xs) -> Cons(x, go(xs, n - 1))
      Cons(x as Lexeme(_, LexInsLCurly), xs) -> Cons(x, go(xs, n - 1))
      Cons(x, xs) -> Cons(x, get-current-block-reverse(xs))
  go(xs0, 0)

// Drops to a matching lexeme using `is-start` and `is-end` to detect nested lexemes
// Assumes the first lexeme is already a start lexeme
fun drop-to-lex-matching(xs: list<lexeme>, is-start: (lex) -> bool, is-end: (lex) -> bool)
  n/drop-to-lex-matching(xs, is-start, is-end, 1)

fun n/drop-to-lex-matching(xs: list<lexeme>, is-start: (lex) -> bool, is-end: (lex) -> bool, n: int)
  match xs
    [] -> []
    Cons(Lexeme(_, l), xs) | l.is-start -> n/drop-to-lex-matching(xs, is-start, is-end, n + 1)
    Cons(Lexeme(_, l), xs) | n > 1 && l.is-end -> n/drop-to-lex-matching(xs, is-start, is-end, n - 1)
    Cons(Lexeme(_, l), xs) | n == 1 -> xs // Dropping from 1 to 0
    Cons(Lexeme(_, l), xs) -> drop-to-lex-matching(xs, is-start, is-end, n)

// Assumes reverse ordered lexemes dropping till we get to actual written code
fun drop-auto-gen-closing(lexes: list<lexeme>)
  match lexes
    [] -> []
    Cons(Lexeme(_, LexInsSemi), xs) -> drop-auto-gen-closing(xs)
    Cons(Lexeme(_, LexInsRCurly), xs) -> drop-auto-gen-closing(xs)
    _ -> lexes

// We should use the lexemes to find the right start token
fun findAt(rm: range-map, p: pos, lexemes: list<lexeme>): maybe<(range, rangeInfo)>
  val lexstart = 
        match lexemes.drop-while(fn(l) !l.range.contains(p))
          Cons(l) -> l.range.start
          _ -> p
  val rinfos = rm.drop-while(fn((r,_)) r.start < lexstart).take-while(fn((r, _)) r.start == lexstart)
  rinfos.prioritize.maybe-head  

fun lexemes-from-pos(lexes: list<lexeme>, p: pos)
  lexes.drop-while(fn(l) !l.range.contains(p))

fun maybe-head(xs: list<a>): maybe<a>
  match xs
    Nil -> Nothing
    Cons(x, _) -> Just(x)

fun find(rm: range-map, r: range)
  rm.filter(fn((r, _)) r == rng)

fun minimum-by-list(xs: list<a>, ?cmp: (a, a) -> order): list<a>
  fun minlist(mx: maybe<list<a>>, y: a, ?cmp: (a, a) -> order): maybe<list<a>>
    Just(
      match mx
        Nothing -> [y]
        Just(Nil) -> [y]
        Just(Cons(x, xs')) ->
          match cmp(x, y)
            Gt -> [y]
            Eq -> Cons(y, Cons(x, xs'))
            _ -> Cons(x, xs')
    )
  xs.foldl(Nothing, minlist).default([])

fun ri-type(ri: rangeInfo)
  match ri
    RIId(_, i) ->
      match i
        NIValue(tp) -> Just(tp)
        NICon(tp) -> Just(tp)
        _ -> Nothing
    _ -> Nothing

fun ri-doc(ri: rangeInfo)
  match ri
    RIId(_, i) ->
      match i
        NIValue(_, _, d) -> Just(d)
        NICon(_, d) -> Just(d)
    _ -> Nothing

fun rm/(|->)(s: sub, rm: range-map): pure range-map
  rm.map(fn((r, ri)) (r, s |-> ri))

fun rm/free-type-vars(rm: range-map): pure tvs
  rm.map(snd).map(free-type-vars).unions

fun rm/bound-type-vars(rm: range-map): pure tvs
  rm.map(snd).map(bound-type-vars).unions

fun ri/(|->)(s: sub, ri: rangeInfo): pure rangeInfo
  match ri
    RIId(nm, i, docs, isDef) -> RIId(nm, s |-> i, docs, isDef)
    _ -> ri

fun ri/free-type-vars(ri: rangeInfo): pure tvs
  match ri
    RIId(_, i) -> free-type-vars(i)
    _ -> emptyTvs

fun ri/bound-type-vars(ri: rangeInfo): pure tvs
  match ri
    RIId(_, i) -> bound-type-vars(i)
    _ -> emptyTvs

fun ni/(|->)(s: sub, ni: nameInfo): pure nameInfo
  match ni
    NIValue(sort, tp, isAnnotated, d) -> NIValue(sort, s |-> tp, isAnnotated, d)
    NICon(tp, d) -> NICon(s |-> tp, d)
    _ -> ni

fun ni/free-type-vars(ni: nameInfo): pure tvs
  match ni
    NIValue(tp) -> free-type-vars(tp)
    NICon(tp) -> free-type-vars(tp)
    _ -> emptyTvs

fun ni/bound-type-vars(ni: nameInfo): pure tvs
  match ni
    NIValue(tp) -> bound-type-vars(tp)
    NICon(tp) -> bound-type-vars(tp)
    _ -> emptyTvs
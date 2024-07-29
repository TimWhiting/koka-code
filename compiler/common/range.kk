//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 7/23/24: Commit 5edd7ce -- missing utfDecode, readInput, extractLiterate

import std/os/path

pub value struct source 
  name: string
  contents: string

val source/null = Source("", "")

pub struct pos
  source: source
  off: int
  line: int
  col: int

val pos/null = Pos(source/null, -1, 0, 0)

fun pos/(==)(p1: pos, p2: pos): bool
  p1.line == p2.line && p1.col == p2.col

fun pos/(<)(p1: pos, p2: pos): bool
  if p1.line < p2.line then
    True
  elif p1.line > p2.line then
    False 
  else
    p1.col < p2.col

fun pos/(<=)(p1: pos, p2: pos): bool
  if p1.line < p2.line then
    True
  elif p1.line > p2.line then
    False 
  else
    p1.col <= p2.col

fun pos/(>)(p1: pos, p2: pos): bool
  if p1.line > p2.line then
    True
  elif p1.line < p2.line then
    False 
  else
    p1.col > p2.col

fun pos/(>=)(p1: pos, p2: pos): bool
  if p1.line > p2.line then
    True
  elif p1.line < p2.line then
    False 
  else
    p1.col >= p2.col

fun pos/cmp(p1: pos, p2: pos): order
  match p1.line.cmp(p2.line)
    Eq -> p1.col.cmp(p2.col)
    o -> o

fun pos/show(p: pos): string
  "(" ++ p.show-pos(?align-width=2) ++ ")"

fun show-pos(p: pos, ?align-width: int): string
  p.line.show-line() ++ "," ++ p.col.show.pad-left(align-width)

fun show-full-pos(p: pos, ?align-width: int): string
  "[" ++ p.off.show ++ "] " ++ p.show-pos()

// about 67 million lines
val big-line: int = 2.pow(26)

fun show-line(line: int)
  if line > big-line then
    "(" ++ (line - big-line).show ++ ")"
  else if line <= 0 then
    "1"
  else
    line.show

fun chars/pos-moves-8(p: pos, cs: list<char>): pos
  cs.foldl(p, pos-move8)

fun sslice/pos-moves8(p: pos, cs: sslice): pos
  cs.string.list.foldl(p, pos-move8)

fun pos-move8(Pos(s, o, l, c), ch: char): pos
  val o1 = if o < 0 then o else o+1
  match ch
    '\t' -> Pos(s, o1, l, ((c + tab-size - 1) / tab-size)*tab-size +1)
    '\n' -> Pos(s, o1, l + 1, 1)
    _    -> Pos(s, o1, l, c + 1)

val tab-size = 2 // Always 2 in koka

// source range
struct range
  start: pos
  end: pos
  hidden: bool

fun range/(==)(r1: range, r2: range): bool
  r1.start == r2.start && r1.end == r2.end && r1.hidden == r2.hidden

fun show-compact-range(r: range)
  "[" ++ r.start.show-pos(0) ++ "," ++ r.end.show-pos(0) ++ "]"

fun show-range(r: range, cwd: path, endToo: bool)
  val path = 
        if r.start.line > big-line then ""
        else  
          r.start.source.name // TODO: Relative to Path cwd
  if endToo then 
    path ++ "(" ++ r.start.show-pos(0) ++ "-" ++ r.end.show-pos(0) ++ ")"
  else path ++ r.start.show

fun range/cmp(r1: range, r2: range): order
  match r1.start.cmp(r2.start)
    Eq -> r1.end.cmp(r2.end)
    o -> o

// Does r2 start after r1
fun range/is-after(r1: range, r2: range): bool
  r1.end <= r2.start

val range/null = make-range(pos/null, pos/null)

fun range/is-null(r: range)
  r.start.off < 0 || r.end.off < 0

fun range/show(r: range): string
  r.show-full-range("".path)

fun show-full-range(r: range, cwd: path): string
  r.show-range(cwd, True)

fun make-range(p1: pos, p2: pos): range
  Range(min(p1, p2), max(p1, p2), False)

fun make-source-range(p: string, l1: int, c1: int, l2: int, c2: int)
  val src = Source(p, "")
  make-range(Pos(src, -1, l1, c1), Pos(src, -1, l2, c2))

fun range/length(r: range): int
  r.end.off - r.start.off

fun source(r: range): source
  r.start.source

fun combine(r1: range, r2: range): range
  Range(min(r1.start, r2.start), max(r1.end, r2.end), r1.hidden || r2.hidden)

fun range-list/combine(rs: list<range>): range
  rs.foldl(range/null, combine)

fun range/hide(r: range)
  Range(r.start, r.end, True)

fun pos/min(p1: pos, p2: pos): pos
  if p1.line <= 0 then // for combining nullRanges sensibly
    p2
  elif p2.line <= 0 then
    p1
  elif (p1 < p2) then
    p1
  else
    p2

fun pos/max(p1: pos, p2: pos): pos
  if (p1 < p2) then
    p2
  else
    p1

fun extend(r: range, off: int): range
  val e = r.end
  Range(r.start, e(col = e.col + off), r.hidden)

// Create a range for the final character in the range
fun end-of-range(r: range): range
  if r.end.off - r.start.off <= 1 then r
  else Range(r.end, r.end, r.hidden)

fun range/contains(r: range, p: pos): bool
  r.start <= p && r.end >= p

fun range/is-before(r: range, p: pos): bool
  r.end < p

fun range/starts-at(r: range, p: pos): bool
  r.start == p

fun range/just-before(r: range): range
  if r.start.off < 0 then r
  else
    match r.start
      Pos(src, off, l, c) -> 
        val newst = Pos(src, off - 1, l, c - 1)
        Range(newst, newst, r.hidden)

fun range/just-after(r: range): range
  if r.end.off < 0 then r
  else
    match r.end
      Pos(src, off, l, c) -> 
        val newst = Pos(src, off + 1, l, c + 1)
        Range(newst, newst, r.hidden)

// From Layout.hs
fun range/after(r: range): range
  Range(r.end, r.end, r.hidden)

// From Layout.hs
fun range/before(r: range): range
  Range(r.start, r.start, r.hidden)

fun range/default(m: maybe<range>): range
  match m
    Just(r) -> r
    Nothing -> null

fun source-from-range(Range(start, end)): string
  if start.off >= 0 then
     " ".replicate(start.col - 1).join ++ start.source.contents.slice.subslice(start.off, end.off).string
  else
    val l1 = if start.line >= big-line then 1 else start.line
    val l2 = if end.line >= big-line then 
        if start.line >= big-line then 
          end.line - start.line + 1 
        else 1
      else end.line
    val c1 = start.col
    val c2 = end.col
    match start.source.contents.lines.drop(l1 - 1).take(l2 - l1 + 1)
      Cons(l, ls) ->
        match (" ".replicate(c1 - 1) ++ Cons(l.list.drop(c1 - 1).string, ls)).reverse
          Cons(ll, lls) -> Cons(ll, lls).take(c2).reverse.unlines
          Nil -> ""
      Nil -> ""

fun raw-source-from-range(Range(start, end)): string
  val s: sslice = start.source.contents.slice
  s.subslice(start.off, end.off).string
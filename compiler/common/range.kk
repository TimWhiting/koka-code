//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

import std/os/path

value struct source (pub name: string, pub contents: string)

val source/null = Source("", "")

struct pos (pub source: source, pub off: int, pub line: int, pub col: int)

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

fun sslice/pos-moves8(cs: sslice, p: pos): pos
  cs.string.list.foldl(p, pos-move8)

fun pos-move8(Pos(s, o, l, c), ch: char): pos
  val o1 = if o < 0 then o else o+1
  match ch
    '\t' -> Pos(s, o1, l, ((c + tab-size - 1) / tab-size)*tab-size +1)
    '\n' -> Pos(s, o1, l + 1, 1)
    _    -> Pos(s, o1, l, c + 1)

val tab-size = 2 // Always 2 in koka

// source range
value struct range (pub start: pos, pub end: pos)

fun range/(==)(r1: range, r2: range): bool
  r1.start == r2.start && r1.end == r2.end

fun show-range(r: range, cwd: path, endToo: bool)
  if r.start.line > big-line then 
    "" 
  else 
    var range := r.start.show-pos(0)
    if endToo then 
      range := "(" ++ r.start.show-pos(0) ++ "-" ++ r.end.show-pos(0) ++ ")"     
    r.start.source.name ++ range

fun range/cmp(r1: range, r2: range): order
  match r1.start.cmp(r2.start)
    Eq -> r1.end.cmp(r2.end)
    o -> o

fun range/length(r: range): int
  r.end.off - r.start.off

// Does r2 start after r1
fun range/is-after(r1: range, r2: range): bool
  r1.end <= r2.start

val range/null = make-range(pos/null, pos/null)

fun range/show(r: range): string
  r.show-full-range("".path)

fun show-full-range(r: range, cwd: path): string
  r.show-range(cwd, True)

fun make-range(p1: pos, p2: pos): range
  Range(min(p1, p2), max(p1, p2))

fun source(r: range): source
  r.start.source

fun combine(r1: range, r2: range): range
  Range(min(r1.start, r2.start), max(r1.end, r2.end))

fun range-list/combine(rs: list<range>): range
  rs.foldl(range/null, combine)

fun range/before(r: range)
  Range(r.start, r.start)

fun range/after(r: range)
  Range(r.end, r.end)

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
  Range(r.start, e(col = e.col + off))

fun default/range(m: maybe<range>): range
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
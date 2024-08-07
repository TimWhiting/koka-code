//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
import compiler/lib/pprint
import compiler/common/failure
import compiler/platform/config
import compiler/common/range
import compiler/common/color-scheme
import compiler/lib/printer
import std/os/path
import std/core-extras
import newstd/test
// Updated as of 7/23/24: Commit: c7c0ac6

// Pretty print helpers
fun pp-range(r: range, cwd: path, endToo: bool)
  r.show-range(cwd, endToo).text.color(colors.colorRange)

fun table(xs: list<(doc, doc)>)
  tablex(0, xs)

fun tablex(n: int, xs: list<(doc, doc)>)
  val headers = xs.map(fst)
  val headerwidth = headers.map(fn(x) x.show.count).maximum
  val doc = 
    if headerwidth <= 0 then vcat(xs.map(snd))
    else vcat(xs.map(fn((hd, d)) hd.fill(headerwidth) |.| colon |+| align(d)))
  doc.indent(n)

// Source from range
fun source-from-ranges(rngs: list<range>)
  rngs.map(source)

fun docs-from-ranges(rngs: list<range>)
  rngs.map(fn(r) r.doc-from-range)

fun doc-from-range(r: range)
  fun remove-indent(ls: list<string>)
    val i = Cons(0, ls.map(fn(l) l.list.take-while(is-space).length)).minimum
    ls.map(fn(l) l.list.drop(i).string)
  fun limit-line-len(line: string, n: int)
    if line.count <= n then line
    else
      val n3 = n / 3
      val (x, y) = line.list.split(2 * n3)
      val pre = x.reverse.drop-while(fn(c) !c.is-space).reverse
      val post = y.reverse.take(n3).reverse.drop-while(fn(c) !c.is-space)
      pre.string ++ " ... " ++ post.string
  fun limit-lines(ls: list<string>, n: int)
    if ls.length <= n then ls.remove-indent
    elif n <= 2 then fail("common/message docFromRange.limitLines: illegal n")
    else
      val n2 = n / 2
      val pre = ls.take(n2)
      val post = ls.reverse.take(n2).reverse
      val prepost = (pre ++ post).remove-indent
      prepost.take(n2) ++ ["..."] ++ prepost.drop(n2)
  val x = r.source-from-range.lines.limit-lines(3).map(fn(l) l.limit-line-len(80))
  match x
    Nil -> pprint/empty
    src -> 
      src.map(text).vcat.align.color(colors.colorSource)

fun test-message()
  with color-scheme-default
  test("tables")
    expect(r#"
Test          : here
Something long: there"#) fn()
      "\n" ++ table([("Test".text, "here".text), ("Something long".text, "there".text)]).show

  test("doc-from-range")
    val source = Source("test.txt", "hello\nworld")
    val start = Pos(source, 0, 1, 1)
    val end = Pos(source, 9, 2, 3)
    expect(r#"hello
wor"#) fn()
      doc-from-range(Range(start, end, False)).show
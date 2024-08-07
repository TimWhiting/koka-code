//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 8/5/24: Commit 5087104, needs is-literal-doc, and extract-literate

// Add braces and semicolons based on layout.

import compiler/syntax/lexeme
import compiler/syntax/lexer
import compiler/syntax/syntax
import compiler/common/range
import compiler/common/name
import std/os/file
import std/os/path
import std/core/undiv
import std/core/unsafe
import std/core-extras

// Lex a source
fun lex-source(source: source, line: int, allow-at: bool, semi-insert: bool, preprocess: list<lexeme> -> <pure|e> list<lexeme>): <pure|e> list<lexeme>
  // val input = if source.name.is-literal-doc then rawinput.extract-literate else rawinput
  val rawinput = source.contents
  lexing(source, line, rawinput).layout(allow-at, semi-insert).preprocess

fun layout(lexemes: list<lexeme>, allow-at: bool, semi-insert: bool): list<lexeme>
  fun semi(v: list<lexeme>, f: (list<lexeme>) -> list<lexeme>) if semi-insert then f(v) else v
  val adjustwhite = lexemes.semi(check-comments)
      .combine-line-comments.remove-whitespace.associate-comments.remove-white
  val at = if allow-at then adjustwhite else adjustwhite.check-ids
  at.semi(indent-layout)

fun is-lex-error(x)
  match x
    LexError(_) -> True
    _ -> False

fun remove-white(lexemes: list<lexeme>): list<lexeme>
  lexemes.filter(fn(x) !is-white(x))

fun remove-whitespace(lexemes: list<lexeme>): list<lexeme>
  lexemes.filter(fn(x) !is-whitespace(x))

// Helpers
fun end-line(r)
  r.end.line

fun start-line(r)
  r.start.line

fun start-col(r)
  r.start.col

fun end-col(r)
  r.end.col

// Range adjust moved to range.kk


val doc-keywords = ["fun","val","ctl","final","raw"
                    ,"type","effect","struct","alias"
                    ,"extern","module"
                    // con
                    // deprecated:
                    ,"control","rcontrol","except","rawctl","brk"
                    ,"cotype","rectype"
                    ,"external","function"]

fun is-doc-keyword(lex: string)
  doc-keywords.find(fn(x) x == lex).bool

fun comment-line(r: range, comment: string)
  if comment.ends-with("\n").bool then r.end.line else r.end.line + 1

fun is-valid-prefix(l: lex): bool
  match l
    LexKeyword -> True // pub
    LexId -> True // inline
    LexInt -> True // fip(1)
    LexSpecial(s) -> ["(", ")", "{", "}", ","].any(fn(x) x == s)
    _ -> False

fun scan-doc-keyword(doc: string, dline: int, acc: ctx<list<lexeme>>, ls: list<lexeme>): maybe<(list<lexeme>, list<lexeme>)>
  match ls
    [] -> Nothing
    Cons(Lexeme(rng)) | rng.start.line != dline -> Nothing
    Cons(Lexeme(r, LexKeyword(k)), rst) | k.is-doc-keyword ->
      Just((acc ++. Cons(Lexeme(r, LexKeyword(k, doc)), Nil), rst))
    Cons(Lexeme(r, LexCons(c)), rst) ->
      Just((acc ++. Cons(Lexeme(r, LexCons(c, doc)), Nil), rst))
    Cons(l as Lexeme(_, lex), rst) ->
      if lex.is-valid-prefix then
        scan-doc-keyword(doc, dline, acc ++ ctx Cons(l, _), rst)
      else Nothing

// Associate comments that precede a declaration
// to the corresponding keyword
fun associate-comments(lexs: list<lexeme>): list<lexeme>
  match lexs
    // Special comments
    Cons(Lexeme(r1, LexComment(c1)), ls) | (c1.starts-with("//.").bool  && !(c1.slice.subslice(3, c1.count).string.trim-right.list.any(is-space))) -> 
        Cons(Lexeme(r1, LexSpecial(c1.trim-right)), ls.associate-comments)
    // Comment association
    Cons(l1 as Lexeme(r1, LexComment(comment)), ls) ->
      match scan-doc-keyword(comment, comment-line(r1, comment), ctx _, ls)
        Just((pre, rest)) -> Cons(l1, pre) ++ rest.pretend-decreasing.associate-comments
        Nothing -> Cons(l1, ls.associate-comments)
    Cons(l,ls) -> Cons(l, ls.associate-comments)
    Nil -> Nil

// Combine adjacent line comments into one block comment (for html output)
fun combine-line-comments(lexs: list<lexeme>): list<lexeme>
  match lexs
    // combine newline comments into one big comment. This is for html output.
    Cons(Lexeme(r1, LexComment(c1)), Cons(Lexeme(r2, LexComment(c2)), ls)) | (c1.starts-with("//").bool && c2.starts-with("//").bool) ->
      combine-line-comments(Cons(Lexeme(r1.combine(r2), LexComment(c1 ++ c2)), ls).pretend-decreasing)
    Cons(l, ls) -> Cons(l, combine-line-comments(ls))
    Nil -> Nil

// -- Check if identifiers contain @ characters
// (these are not generally allowed in user programs but are exposed
//  in kki files and primitive modules (std/core/types, std/core/hnd))
fun check-ids(lexs: list<lexeme>): list<lexeme>
  match lexs
    Nil -> Nil
    Cons(lex1 as Lexeme(_, LexKeyword(keyw)), Cons(lex2 as Lexeme(_, LexId), lexes)) | ["fun", "val", "extern"].any(fn(n) n == keyw) ->
      // Ok to define @ functions
      Cons(lex1, Cons(lex2, lexes.check-ids))
    Cons(l as Lexeme(rng, lex), lexes) ->
      fun check-id(idn: name)
        if idn.nameStem.list.any(fn(c) c == '@') then
          Cons(Lexeme(rng, LexError("\"@\": identifiers cannot contain '@' characters (in '" ++ idn.show ++ "')")), lexes.check-ids)
        else
          lexes
      val lexes' = match lex
        LexId(id) -> id.check-id
        LexCons(id) -> id.check-id
        LexOp(id) -> id.check-id
        LexPrefix(id) -> id.check-id
        LexIdOp(id) -> id.check-id
        LexWildCard(id) -> id.check-id
        _ -> lexes.check-ids
      Cons(l, lexes')

// Check for comments in indentation
fun check-comments(lexs: list<lexeme>): list<lexeme>
  check(0, range/null, lexs)

fun check(prev-line: int, comment-rng: range, l: list<lexeme>): list<lexeme>
  match l
    Nil -> Nil
    Cons(Lexeme(rng, lex), ls) -> 
      val newR = match lex
        LexComment(s) | s.starts-with("\n#").bool.not -> check(prev-line, rng, ls)
        LexWhite -> check(prev-line, comment-rng, ls)
        _ -> check-indent(prev-line, rng, comment-rng) ++ check(rng.end-line, comment-rng, ls)
      Cons(Lexeme(rng, lex), newR)

fun check-indent(prev-line: int, rng: range, comment-rng: range)
  if rng.start-line > prev-line && rng.start-line == comment-rng.end-line && comment-rng.end-col > 1 then 
  // For wrap-around line columns
    [Lexeme(comment-rng, LexError("layout: comments cannot be placed in the indentation of a line"))]
  else Nil

// Brace and Semicolon insertion
// Assumes whitespace is already filtered out
value struct layout
  open: lexeme
  column: int

fun indent-layout(lexs: list<lexeme>): list<lexeme>
  match lexs
    Nil -> Cons(Lexeme(range/null, LexInsSemi), Nil)
    Cons(l, _) -> 
      val start = Lexeme(l.range.before, LexWhite("")) // ignored
      pretend-no-div
        brace(Layout(start, 1), [], start, lexs)

fun brace(layout: layout, layouts: list<layout>, prev: lexeme, lexemes: list<lexeme>): <div> list<lexeme>
  match lexemes
    Nil -> // End of file
      match layouts
        Nil -> Nil 
        Cons(ly, lys) -> // End of file ending braces
          val rcurly = layout.insert-rcurly(prev)
          prev.insert-semi ++ rcurly ++ brace(ly, lys, Lexeme(prev.range.after, LexInsRCurly), [])
    // ignore error lexemes
    Cons(l, ls) | l.lex.is-error -> Cons(l, brace(layout, layouts, prev, ls))
    Cons(lexeme as Lexeme(rng, lex), ls) -> 
      val Layout(Lexeme(_, layout-lex), layout-col) = layout
      val Lexeme(prevRng, prev-lex) = prev
      val newline = prevRng.end-line < rng.start-line
      val indent = rng.start-col
      val nextIndent = match ls
        Cons(Lexeme(r, _), _) -> r.start-col
        _ -> 1
      // insert {
      if newline && indent > layout-col && !(prev-lex.is-expr-continuation(lex)) then
        brace(layout, layouts, prev, prev.insert-lcurly ++ lexemes)
      // insert }
      elif newline && indent < layout-col && !(lex.is-close-brace && layout-lex == LexSpecial("{")) then
        brace(layout, layouts, prev, layout.insert-rcurly(prev) ++ lexemes)
      // push new layout
      elif lex.is-open-brace then
        val v = if (nextIndent > layout-col) then [] else [Lexeme(rng, LexError("layout: line must be indented more than the enclosing layout context (column " ++ layout-col.show ++ ")"))]
        [lexeme] ++ v ++ brace(Layout(lexeme, nextIndent), Cons(layout, layouts), lexeme, ls)
      // pop layout
      elif lex.is-close-brace then
        val rest = match layouts
          Nil -> Cons(Lexeme(rng.before, LexError("unmatched closing brace '}'")), brace(layout, [], lexeme, ls))
          Cons(ly, lys) -> brace(ly, lys, lexeme, ls)
        prev.insert-semi ++ Cons(lexeme, rest)
      // semicolon insertion
      elif newline && indent == layout-col && !(prev-lex.is-expr-continuation(lex)) then
        prev.insert-semi ++ [lexeme] ++ brace(layout, layouts, lexeme, ls)
      else
        Cons(lexeme, brace(layout, layouts, lexeme, ls))

fun insert-lcurly(Lexeme(prev-rng, _))
  [Lexeme(prev-rng.after, LexInsLCurly)]

fun insert-rcurly(Layout(Lexeme(layout-rng, layout-lex), layout-col), Lexeme(prev-rng, _)): list<lexeme>
  val start = 
        if layout-lex == LexInsLCurly then [] 
        else [Lexeme(prev-rng.after, 
          LexError(
            "layout: an open brace '{' (at " ++ layout-rng.show-range("".path, True) ++ 
            ", layout column " ++ layout-col.show  ++ ") is matched by an implicit closing brace"
          ))]
  start ++ Cons(Lexeme(prev-rng.after, LexInsRCurly), Nil)

fun insert-semi(Lexeme(prev-rng, prev-lex))
  if prev-lex.isSemi then [] else [Lexeme(prev-rng.after, LexInsSemi)]

fun is-expr-continuation(prev-lex, lex)
  lex.is-start-continuation-token || prev-lex.is-end-continuation-token

fun is-start-continuation-token(lex)
  match lex
    LexSpecial(s) -> [")",">","]",",","{","}"].any(fn(c) c == s)
    LexKeyword(k, _) -> ["then","else","elif","->","=","|",":",".",":="].any(fn(c) c == k)
    LexOp(op) -> op.nameStem != "<"
    LexInsLCurly -> True
    LexInsRCurly -> True
    _ -> False

fun is-end-continuation-token(lex)
  match lex
    LexSpecial(s) -> ["(","<","[",",","{"].any(fn(c) c == s)
    LexKeyword(k, _) -> k == "."
    LexInsLCurly -> True
    LexOp(op) -> op.nameStem != ">"
    _ -> False

inline fun is-close-brace(lex)
  match lex
    LexSpecial("}") -> True
    LexInsRCurly -> True
    _ -> False

inline fun is-open-brace(lex)
  match lex
    LexSpecial("{") -> True
    LexInsLCurly -> True
    _ -> False

inline fun isSemi(lex)
  match lex
    LexSpecial(";") -> True
    LexInsSemi -> True
    _ -> False
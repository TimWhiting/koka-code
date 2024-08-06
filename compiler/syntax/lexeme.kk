//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 8/5/24: Commit 680b2b8

import std/os/path
import std/text/regex
import std/text/unicode
import std/num/float64
import std/core/undiv
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/common/id

val typeVarRegex = "^[a-z][0-9]*$".regex();

pub fun isTypeVar(n: name): bool
  !typeVarRegex.exec(n.nameStem).is-empty

// Lexer tokens
// A lexical token with an associated range.
pub value struct lexeme
  range: range
  lex: lex

// A lexical token.
pub type lex
  LexInt(i: int, s: string) // String is original number, used for documentation
  LexFloat(f: float64, s: string) // String is original number, used for documentation
  LexChar(c: char)
  LexString(s: string)
  LexId(n: name)
  LexCons(n: name, s: string = "") // Can have a doc attached
  LexOp(n: name)
  LexPrefix(n: name)
  LexIdOp(n: name)
  LexWildCard(n: name)
  LexKeyword(s: string, k: string) 
  LexSpecial(s: string)
  LexComment(s: string)
  LexWhite(s: string)
  // Special for highlighting
  LexModule(alias_: name, full: name) // alias full-import
  LexTypedId(n: name, s: string)
  LexInsLCurly // Inserted '{'
  LexInsRCurly // Inserted '}'
  LexInsSemi // Inserted ';'
  LexError(s: string) // layout errors

// 'True' when the lexeme is whitespace
pub fun lexeme/is-white(l: lexeme): <> bool
  l.lex.is-white

// 'True' when the lexical token is whitespace
pub fun lex/is-white(l: lex): <> bool
  match l
    LexWhite -> True
    LexComment -> True
    _ -> False

// 'True' when the lexical token is exactly LexWhite
pub fun lexeme/is-whitespace(l: lexeme): <> bool
  l.lex.is-whitespace

// 'True' when the lexical token is exactly LexWhite
pub fun lex/is-whitespace(l: lex): <> bool
  match l
    LexWhite(_) -> True
    _ -> False

// Returns 'True' if the lexical tokens of the lexeme are of the same kind. (i.e. Constructor)
pub fun same-lexeme(Lexeme(_, lex1): lexeme, Lexeme(_, lex2): lexeme): <> bool
  match (lex1, lex2)
    (LexKeyword(n1, _), LexKeyword(n2, _)) -> n1 == n2 
    (LexSpecial(n1), LexSpecial(n2)) -> n1 == n2
    _ -> lex1.from-enum == lex2.from-enum

pub fun from-enum(l: lex): <> int
  match l
    LexInt -> 0
    LexFloat -> 1
    LexChar -> 2
    LexString -> 3
    LexId -> 4
    LexOp -> 5
    LexPrefix -> 19
    LexIdOp -> 20
    LexWildCard -> 6
    LexModule -> 7
    LexKeyword -> 8
    LexSpecial -> 9
    LexComment -> 10
    LexWhite -> 11
    LexInsLCurly -> 13
    LexInsRCurly -> 14
    LexInsSemi -> 15
    LexError -> 16
    LexCons -> 17
    LexTypedId -> 18

pub fun lexeme/show(Lexeme(rng, lex): lexeme): <> string
  rng.show-full-range("".path) ++ ": " ++ lex.show

pub fun lex/show(l: lex): <> string
  match l
    LexInt(_, s) -> s
    LexFloat(_, s) -> s
    LexChar(c) -> c.show
    LexString(s) -> s.show
    LexId(n) -> "identifier \"" ++ n.show ++ "\""
    LexOp(n) -> "operator \"" ++ n.show ++ "\""
    LexPrefix(n) -> "prefix operator \"" ++ n.show ++ "\""
    LexIdOp(n) -> "identifier (operator) \"" ++ n.show ++ "\""
    LexWildCard(n) -> "wildcard \"" ++ n.show ++ "\""
    LexModule(n, _) -> "module \"" ++ n.show ++ "\""
    LexKeyword(k, d) -> "\"" ++ k ++ "\"" ++ (if d.is-empty then "" else " (" ++ d ++ ")")
    LexSpecial(s) -> "\"" ++ s ++ "\""
    LexComment(s) -> "comment \"" ++ s ++ "\""
    LexWhite -> "white"
    LexInsLCurly -> "start of statements ('{')"
    LexInsRCurly -> "end of statements ('}')"
    LexInsSemi -> "end of statement (';')"
    LexError(msg) -> msg
    LexCons(n) -> "constructor \"" ++ n.show ++ "\""
    LexTypedId(n, tp) -> "typedid " ++ n.show ++ ":" ++ tp

fun is-lcurly(l: lex): bool
  match l
    LexInsLCurly -> True
    LexSpecial("{") -> True
    _ -> False

fun is-rcurly(l: lex): bool
  match l
    LexInsRCurly -> True
    LexSpecial("}") -> True
    _ -> False

fun is-rparen(l: lex): bool
  match l
    LexSpecial(")") -> True
    _ -> False

fun is-lparen(l: lex): bool
  match l
    LexSpecial("(") -> True
    _ -> False

fun is-rangle(l: lex): bool
  match l
    LexSpecial(">") -> True
    LexOp(nm) | nm.show-plain == ">" -> True
    _ -> False

fun is-langle(l: lex): bool
  match l
    LexSpecial("<") -> True
    LexOp(nm) | nm.show-plain == "<" -> True
    _ -> False

fun is-rbracket(l: lex): bool
  match l
    LexSpecial("]") -> True
    _ -> False

fun is-lbracket(l: lex): bool
  match l
    LexSpecial("[") -> True
    _ -> False

pub fun lexeme/(==)(l1: lexeme, l2: lexeme): bool
  l1.range == l2.range && l1.lex == l2.lex

pub fun lex/(==)(l1: lex, l2: lex): bool
  match (l1, l2)
    (LexInt(i1, s1), LexInt(i2, s2)) -> i1 == i2 && s1 == s2
    (LexFloat(f1, s1), LexFloat(f2, s2)) -> f1 == f2 && s1 == s2
    (LexChar(c1), LexChar(c2)) -> c1 == c2
    (LexString(s1), LexString(s2)) -> s1 == s2
    (LexId(n1), LexId(n2)) -> n1 == n2
    (LexCons(n1, d1), LexCons(n2, d2)) -> n1 == n2 && d1 == d2
    (LexOp(n1), LexOp(n2)) -> n1 == n2
    (LexPrefix(n1), LexPrefix(n2)) -> n1 == n2
    (LexIdOp(n1), LexIdOp(n2)) -> n1 == n2
    (LexWildCard(n1), LexWildCard(n2)) -> n1 == n2
    (LexKeyword(s1, k1), LexKeyword(s2, k2)) -> s1 == s2 && k1 == k2
    (LexSpecial(s1), LexSpecial(s2)) -> s1 == s2
    (LexComment(s1), LexComment(s2)) -> s1 == s2
    (LexWhite(s1), LexWhite(s2)) -> s1 == s2
    (LexModule(a1, f1), LexModule(a2, f2)) -> a1 == a2 && f1 == f2
    (LexTypedId(n1, s1), LexTypedId(n2, s2)) -> n1 == n2 && s1 == s2
    (LexInsLCurly, LexInsLCurly) -> True
    (LexInsRCurly, LexInsRCurly) -> True
    (LexInsSemi, LexInsSemi) -> True
    (LexError(s1), LexError(s2)) -> s1 == s2
    _ -> False

pub fun lex/is-error(l: lex)
  match l
    LexError(_) -> True
    _ -> False

pub fun is-semicolon(l: lexeme): bool
  match l.lex
    LexInsSemi -> True
    LexSpecial(";") -> True
    _ -> False

// Lexical Imports
struct lex-import
  name: name
  imp-alias: name
  vis: visibility
  is-open: bool

fun lex-import/show(Lex-import(nm, al, vis, open): lex-import): string
  if vis.is-public then "pub " else "" ++
  (if open then "@open" else "") ++
  (if al.is-nil then "" else al.show ++ " = ") ++
  nm.show

fun lex-import/(==)(i1: lex-import, i2: lex-import): bool
  i1.name == i2.name // consider equal import names

// remove duplicates
fun lex-import-nub(l: list<lex-import>): list<lex-import>
  match l
    Nil -> Nil
    Cons(li, lis) ->
      match lis.find(fn(i2) li == i2)
        Just(li') -> 
          val li2 = 
            Lex-import(
              li.name, 
              if li.imp-alias.is-nil then li'.imp-alias else li.imp-alias,
              if li.vis.is-public || li'.vis.is-public then Public else Private,
              li.is-open || li'.is-open
            )
          Cons(li2, lis.delete(li).pretend-decreasing.lex-import-nub)
        Nothing -> Cons(li, lis.pretend-decreasing.lex-import-nub)

fun delete(l: list<lex-import>, i: lex-import): list<lex-import>
  match l
    Nil -> Nil
    Cons(h, t) -> if h == i then t else Cons(h, t.delete(i))
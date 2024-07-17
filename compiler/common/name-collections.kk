//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

import std/data/linearmap
import std/data/linearset
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import newstd/test

alias name-map<a> = linearMap<name, a>;

alias nameSet = linearSet<name>;
val names/empty: nameSet = LinearSet([])

alias qname-map<a> = linearMap<name,list<(name,a)>>;

fun name-map/find(m: name-map<a>, n: name): <div,exn> a
  match m.lookup(n)
    Just(x) -> x
    _ -> throw("common/name-map/find: could not find: " ++ n.show)

type lookup<a>
  Found(name: (name, a))
  Ambiguous(names: list<name>)
  NotFound

fun lookup/(==)(a: lookup<a>, b: lookup<a>, ?(==): (a,a) -> e bool): e bool
  match (a, b)
    (Found(x), Found(y)) -> x.fst == y.fst && x.snd == y.snd
    (Ambiguous(xs), Ambiguous(ys)) -> list/(==)(xs, ys)
    (NotFound, NotFound) -> True
    _ -> False

fun lookup/show(a: lookup<a>, ?show: (a) -> e string): e string
  match a
    Found((name, _)) -> "Found(" ++ name.show ++ ")"
    Ambiguous(names) -> "Ambiguous(" ++ names.map(fn(n) n.show).list/show ++ ")"
    NotFound -> "NotFound"

fun qname-map/single(n: name, a: a): qname-map<a>
  LinearMap([(n.unqualify, [(n, a)])])

fun qname-map/from-list(l: list<(name,a)>): <comp-flags,pure> qname-map<a>
  l.foldl(LinearMap([])) fn(qm, (name, x))
    qm.insert(name, x)

// Lookup a fully qualified name
fun qname-map/lookup-qualified(m: qname-map<a>, n: name): maybe<a>
  match m.lookup(n.unqualify)
    Just(xs) -> xs.lookup(fn(o) o == n)
    _ -> Nothing

// Lookup a potentially unqualified name within a module context. 
// (The module context is ignored if a qualified name is looked up)
fun qname-map/lookup(m: qname-map<a>, c: name, name: name): lookup<a>
  match m.lookup(name.unqualify)
    Just(Cons((qname,x), _)) | !name.is-qualified -> Found((qname, x))
    Just(xs) ->
      val qname = if name.is-qualified then name else c.qualify(name)
      match xs.filter(fn((n, _)) -> n == qname)
        Cons((realname, x), _) -> Found((realname, x))
        _ -> Ambiguous(xs.map(fst))
    _ -> NotFound

fun qname-map/filter-names(m: qname-map<a>, p: (name) -> e bool): e qname-map<a>
  m.map fn(k, xs) 
    (k, xs.filter(fn((n, _)) p(n)))

fun qname-map/insert(m: qname-map<a>, n: name, a: a): <comp-flags,exn> qname-map<a>
  m.update(n.unqualify, Cons((n, a), Nil)) fn(xs, ys)
    safe-combine("insert", xs, ys)

fun qname-map/union(m1: qname-map<a>, m2: qname-map<a>): <comp-flags,exn> qname-map<a>
  m1.union-with(m2) fn(xs, ys)
    safe-combine("union", xs, ys)

fun qname-map/union-left-bias(m1: qname-map<a>, m2: qname-map<a>): <comp-flags,exn> qname-map<a>
  m1.union-with(m2, (++))

fun qname-map/unions(ms: list<qname-map<a>>): <comp-flags,exn> qname-map<a>
  ms.foldl(LinearMap([])) fn(m1, m2)
    m1.union(m2)

fun qname-map/safe-combine(s: string, xs: list<(name,a)>, ys: list<(name,a)>): <comp-flags,exn> list<(name,a)>
  if xs.any(fn(x) ys.any(fn(y) y.fst == x.fst)) then
    fail("common/name-collections " ++ s ++ ": overlapping names: " ++ xs.map(fn((x, _)) x).list/show ++ ys.map(fn((y,_)) y).list/show)
  xs ++ ys

fun test-name-collections()
  test("Qualified Name Map")
    val qname1 = "hello/world".read-qualified-name
    expect(Found((qname1, 0))) fn()
      single(qname1, 0).lookup("".new-name, "world".new-name)
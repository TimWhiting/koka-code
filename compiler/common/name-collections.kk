//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

import newstd/data/linearmap
import newstd/data/linearset
import compiler/common/name
import compiler/common/failure
import compiler/platform/config

alias name-map<a> = linearMap<name, a>;

fun find(m: name-map<a>, n: name): <div,exn> a
  match m.maybe-get(n)
    Just(x) -> x
    _ -> throw("common/name-map.find: could not find: " ++ n.name/name/show)

alias nameSet = linearSet<name>;
val names/empty = []

alias qname-map<a> = linearMap<name,list<(name,a)>>;

type lookup<a>
  Found(name: (name, a))
  Ambiguous(names: list<name>)
  NotFound

fun qname/empty(): qname-map<a>
  []

fun single(n: name, a: a): qname-map<a>
  [(n.unqualify, [(n, a)])]

fun insert(m: qname-map<a>, n: name, a: a): <comp-flags,exn> qname-map<a>
  m.update(n.unqualify, Cons((n, a), Nil)) fn(xs, ys)
    safe-combine("insert", xs, ys)

fun from-list(l: list<(name,a)>): <comp-flags,pure> qname-map<a>
  l.foldl([]) fn(qm, (name, x))
    qm.insert(name, x)

fun safe-combine(s: string, xs: list<(name,a)>, ys: list<(name,a)>): <comp-flags,exn> list<(name,a)>
  if xs.any(fn(x) ys.any(fn(y) y.fst == x.fst)) then
    fail("common/name-collections " ++ s ++ ": overlapping names: " ++ xs.map(fn((x, _)) x).list/show(?show=name/name/show) ++ ys.map(fn((y,_)) y).list/show(?show=name/name/show))
  xs ++ ys

// Lookup a fully qualified name
fun lookupQ(m: qname-map<a>, n: name): maybe<a>
  match m.maybe-get(n.unqualify)
    Just(xs) -> xs.lookup(fn(o) o == n)
    _ -> Nothing

// Lookup a potentially unqualified name within a module context. 
// (The module context is ignored if a qualified name is looked up)
fun lookup(m: qname-map<a>, c: name, name: name): lookup<a>
  match m.maybe-get(name.unqualify)
    Just(Cons((qname,x), _)) | !name.is-qualified -> Found((qname, x))
    Just(xs) ->
      val qname = if name.is-qualified then name else c.qualify(name)
      match xs.filter(fn((n, _)) -> n == qname)
        Cons((realname, x), _) -> Found((realname, x))
        _ -> Ambiguous(xs.map(fst))
    _ -> NotFound

fun filter-names(m: qname-map<a>, p: (name) -> e bool): e qname-map<a>
  m.map fn(k, xs) 
    (k, xs.filter(fn((n, _)) p(n)))
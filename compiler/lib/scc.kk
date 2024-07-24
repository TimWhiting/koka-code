//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 7/23/24: Commit b8074c2

import std/data/linearmap
import std/data/linearset
import compiler/common/name-collections
import std/core/undiv
import std/core/unsafe

alias graph<v> = linearMap<v, list<v>>;
alias edge<v> = (v,v)
alias node<v> = (v,list<v>)

fun nodes(g: graph<v>): list<node<v>>
  g.list

fun graph(es: list<node<v>>): graph<v>
  LinearMap(es)

fun edges(g: graph<v>): list<edge<v>>
  with v <- g.nodes.flatmap
  with w <- v.snd.map
  (v.fst, w)

fun vertices(g: graph<v>): list<v>
  g.nodes.map(fst)

fun successors(g: graph<v>, v: v, ?(==): (v, v) -> e bool): e list<v>
  g.get-default(v, [])

fun transpose(g: graph<v>, ?a/(==): (v,v) -> e bool): e graph<v>
  fun add(e: edge<v>, m:graph<v>, ?b/(==): (v,v) -> e bool): e graph<v>
    m.update(e.snd, [], fn(o, r) Cons(e.fst, r))
  g.edges.foldr(g.map(fn (k, v) (k, [])), fn(a, b) a.add(b))

rec type tree<v>
  Tree
    head: v
    fs: forest<v>

rec type forest<v>
  Forest
    list: list<tree<v>>

fun dff(g: graph<v>, ?(==): (v,v) -> bool): forest<v>
  g.dfs(g.vertices)

fun dfs(g: graph<v>, vs: list<v>, ?(==): (v, v) -> bool): forest<v>
  with unsafe-total
  Forest(vs.map(fn(v) g.tree(v, ref(LinearSet([v]))))).prune()

fun tree(g: graph<v>, v: v, visited: ref<h, linearSet<v>>, ?(==): (v, v) -> div bool): <div,read<h>,write<h>> tree<v>
  val f = g.successors(v).flatmap fn(v')
    if (!visited).member(v') then []
    else
      visited.set((!visited).add(v'))
      [g.tree(v'.pretend-decreasing, visited)]
  Tree(v, Forest(f))

alias vset<v> = linearSet<v>;

fun prune(fs: forest<v>, ?a/(==): (v,v) -> bool): forest<v>
  fun chop(ms: vset<v>, fs1: forest<v>, ?v/(==): (v,v) -> bool): (vset<v>, forest<v>)
    match fs1.list
      [] -> (ms, Forest([]))
      Cons(Tree(v, vs), fs2) ->
        if ms.member(v) then chop(ms.pretend-decreasing, Forest(fs2))
        else
          val ms0 = ms.add(v)
          val (ms1, vs') = chop(ms0.pretend-decreasing, vs.pretend-decreasing)
          val (ms2, fs2') = chop(ms1.pretend-decreasing, Forest(fs2).pretend-decreasing)
          (ms2, Forest(Cons(Tree(v, vs'), fs2'.list)))
  LinearSet([]).chop(fs).snd

fun preorder(g: graph<v>, ?(==): (v,v) -> bool): list<v>
  with unsafe-total
  g.dff.preorderF

fun preorderF(f: forest<v>): div list<v>
  f.list.flatmap(preorderT)

fun preorderT(t: tree<v>): div list<v>
  Cons(t.head, t.fs.preorderF)

fun postorder(g: graph<v>, ?(==): (v,v) -> bool): list<v>
  g.dff.postorderF

pub fun postorderF(f: forest<v>): list<v>
  with unsafe-total
  postorderF'(f.list, [])

fun postorderT'(t: tree<v>, vs: list<v>): div list<v>
  postorderF'(t.fs.list, Cons(t.head, vs))

fun postorderF'(ts: list<tree<v>>, vs: list<v>): div list<v>
  match ts
    [] -> vs
    Cons(t, ts') -> postorderT'(t, postorderF'(ts', vs))

fun scc(nodes: list<node<v>>, ?(==): (v, v) -> bool): div list<list<v>>
  sccG(nodes.graph)

fun sccG(g: graph<v>, ?(==): (v,v) -> bool): list<list<v>>
  with unsafe-total
  g.sccF.map(preorderT)

fun sccF(g: graph<v>, ?(==): (v,v) -> bool): list<tree<v>>
  g.transpose.dfs(g.topsort).list.reverse

fun topsort(g: graph<v>, ?(==): (v,v) -> bool): list<v>
  g.postorder.reverse

fun reachable(g: graph<v>, v: v, ?(==): (v,v) -> bool): list<v>
  with unsafe-total
  g.dfs([v]).preorderF

fun path(g: graph<v>, v: v, w: v, ?(==): (v,v) -> bool): bool
  g.reachable(v).find(fn(e) e == w).is-just

// fun main()
//   // "".println
//   scc([(0,[1]),(1,[1,2,3]),(2,[1]),(3,[]),(4,[])], (==)).show-list(fn(l) l.show-list(show)).println
//   scc([('a',"jg".list)
//     ,  ('b',"ia".list)
//     ,  ('c',"he".list)
//     ,  ('d',"".list)
//     ,  ('e',"jhd".list)
//     ,  ('f',"i".list)
//     ,  ('g',"fb".list)
//     ,  ('h',"".list)], (==)).show-list(fn(l) l.show-list(show)).println

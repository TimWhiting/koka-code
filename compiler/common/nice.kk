//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
import compiler/common/id
import compiler/type/type
import compiler/lib/pprint
import compiler/kind/kind
import compiler/common/syntax
import std/data/linearmap
import newstd/test

// Map identifiers to /nice/ strings.
alias nice = id-map<string>

effect niceEff<k>
  fun extend-nice(tv: k): ()
  fun get-nice(tv: k): string 
  fun get-nice-doc(tv: k): doc 

fun niceEnv(f)
  var nice := []
  var effectIndex := -1
  var heapIndex := -1
  var typeIndex := -1
  var typeLetterIndex := -1
  var scopeIndex := -1
  with handler
    fun extend-nice(tv: typeVar)
      val x = 
        if tv.kind == kindEffect then
          effectIndex := effectIndex + 1
          "e" ++ (if effectIndex == 0 then "" else effectIndex.show-id)
        elif tv.kind == kindHeap then
          heapIndex := heapIndex + 1
          "h" ++ (if heapIndex == 0 then "" else heapIndex.show-id)
        elif tv.kind == kindScope then
          scopeIndex := scopeIndex + 1
          "s" ++ (if scopeIndex == 0 then "" else scopeIndex.show-id)
        else
          match typeLetterIndex
            4 -> 
              typeIndex := typeIndex + 1
              typeLetterIndex := 0
            _ ->
              typeLetterIndex := typeLetterIndex + 1
          (typeLetterIndex + 'a'.int).char.string ++ (if typeIndex == 0 then "" else typeIndex.show-id)
      nice := nice.extend(tv.tid, x)
      ()
    fun get-nice(tv: typeVar)
      nice.nice/show(tv.tid)
    fun get-nice-doc(tv: typeVar)
      nice.nice/pretty(tv.tid)
  f()

// Add fresh identifier substitutions give an (infinite) list of nice names.
fun extend(n: nice, id: int, name: string): nice
  n.set(id, name)

// Show the nice version of an identifier
fun nice/show(n: nice, id: id): string
  match n.maybe-get(id)
    Just(name) -> name
    Nothing -> id.show-id

// Pretty print an identifier nicely.
fun nice/pretty(n: nice, id: id): doc
  n.nice/show(id).text

/// Tests for identifiers
fun test-ids()
  test("ids")
    expect({id-nil.new-id.new-id-from}, 1, "new-id")
    expect({gen-id("test", 1).show-id}, "\"1\"", "show-id")
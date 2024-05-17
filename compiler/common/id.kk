//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
import std/data/linearmap
import std/data/linearset
import compiler/lib/pprint

/// Internal identifiers (just 'Int's).

/// Types aliases
/// A list of identifiers
alias ids = list<id>
// A map from identifiers to values
alias id-map<a> = linearMap<int, a>
// A set of identifiers
alias id-set = linearSet<int>

/// Identifiers are unique compiler generated identities
alias id = int;

/// Show quotes around the id
fun show-id(id: id): <> string
  "\"" ++ id.int/show ++ "\""

/// Generate an 'Id' with a certain base name (which is ignored :-)
fun gen-id(baseName: string, i: int): <> id
  i.new-id

/// Create a fresh identifier
fun new-id(i: int): <> id
  i

fun new-id-from(id: id): <> id
  id + 1

/// Dummy identifier
val id-nil = 0.new-id

/// Only used internally to guarantee unique identifiers
fun id-number(id: id): <> int
  id

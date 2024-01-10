import compiler/platform/config

pub alias compilerEff = <comp-flags, exn>

fun raise(s: string): compilerEff a
  if comp-flags.buildVariant == "debug" then 
    throw(s) // Figure out stack traces
  else throw(s)

fun fail(s: string): compilerEff a
  raise("*** internal compiler error " ++ s)

fun assert(s: string, b: bool, a: a): compilerEff a
  if b then a else fail(s)

fun todo(s: string): compilerEff a
  fail("todo: " ++ s)
pub import compiler/platform/config
import newstd/core

pub alias compilerEff = <comp-flags, exn>

fun raise(s: string): exn a
  // if comp-flags.buildVariant == "debug" then 
  //   throw(s) // Figure out stack traces
  // else 
  throw(s)

fun fail(s: string): exn a
  raise("*** internal compiler error " ++ s)

fun assert(s: string, b: bool, a: a): exn a
  if b then a else fail(s)

fun todo(s: string): exn a
  fail("todo: " ++ s)

fun catch(hndl: string -> e a, f: () -> <exn|e> a): e a
  fun adjust(s: string): string
    s // TODO: Adjust any errors if needed
  with handler final ctl throw-exn(e)
    hndl(e.message.adjust)
  f()




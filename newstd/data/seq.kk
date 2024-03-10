

type seq<a>
  SNil
  SCons(value: a, values: seq<(a,a)>)

fun sizeS(s: seq<a>)
  match s
    SNil -> 0
    SCons(_,ps) -> 1 + 2 * ps.sizeS

fun main()
  SCons(1, SCons((1, 1), SNil)).sizeS.println
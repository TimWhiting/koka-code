type ktype
  TForAll(r: ktype) // Cannot make this rho
  TDefault()

alias rho = ktype // unqualified type

extern cast(a: a): <> b
  c inline "#1"

fun maxSynonymRank(t: rho): int
  match t
    TForAll(r) -> maxSynonymRank(r.cast.unsafe-decreasing)
    TDefault() -> 0

fun main(): <console> ()
  val h = TForAll(TDefault.cast)
  maxSynonymRank(h).println

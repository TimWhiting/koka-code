
alias rho = ktype // unqualified type

type ktype
  TForAll(r: rho)
  TDefault()

fun maxSynonymRank(t: rho): int
  match t
    TForAll(r) -> maxSynonymRank(r)
    TDefault() -> 0

fun main(): <console> ()
  val h = TForAll(TDefault)
  maxSynonymRank(h).println

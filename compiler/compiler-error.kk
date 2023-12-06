import newstd/data/linearset
import compiler/common/name
import compiler/common/name-collections

alias deps = linearSet<name>
fun depsUnions(l: list<deps>): deps
  l.foldl(namesEmpty, fn(s: deps, a: deps) s + a)
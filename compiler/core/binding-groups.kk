import compiler/lib/scc
import compiler/core/core
import compiler/core/corevar
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap
import std/data/linearset

// Re-analyze a recursive binding group just after type checking.
// Due to overloading, functions that seem mutually recursive may not
// actually be mutually recursive after the types are resolved.
alias deps = linearMap<tName, linearSet<tName>>
alias freeVar = linearSet<tName>

// Re-analyze a recursive binding group and return a list of new
// definition groups. After type checking it is possible that definitions
// that seemed recursive are actually not mutually recursive.

fun regroup(dfs: list<def>): <comp-flags,pure> list<defGroup>
  match dfs
    Cons(d, Nil) ->
      val fvdef = d.free-vars
      //  this is for recursive definitions where the type may still differ since we cannot improve too early for mutual recursive definitions (or we unify too eagerly, see "while")
      if fvdef.member(TName(d.def-name, d.ktype)) || 
        fvdef.list.map(get-name).filter(fn(n) !n.is-qualified).any(fn(dn) dn == d.def-name) then
        [DefRec([d])]
      else
        [DefNonRec(d)]
    defs ->
      val def-names = defs.map(fn(d) TName(d.def-name, d.ktype))
      val def-nameSet = LinearSet(def-names)
      val defMap = LinearMap(def-names.zip(defs))
      val deps = LinearMap(def-names.zip(defs.map(fn(d) d.free-vars.intersection(def-nameSet))))
      // determine strongly connected components
      val defOrder = deps.list.map(fn((nm, fvs)) (nm, fvs.linearset/list)).scc
      // create a definition group
      fun makeGroup(names)
        match names
          [nm] -> 
            if deps.get(nm).member(nm) then DefRec([defMap.get(nm)])
            else DefNonRec(defMap.get(nm))
          _ -> DefRec(names.map(fn(nm) defMap.get(nm)))
      defOrder.map(makeGroup)

fun find(nameMap: list<(tName, b)>, nm: tName): <comp-flags,exn> b
  match find(nameMap, fn(n: (tName,b)) n.fst == nm)
    Just(x) -> x.snd
    _ -> fail("core/binding-groups find: could not find: " ++ nm.show)



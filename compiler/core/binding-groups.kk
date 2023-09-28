import compiler/lib/scc
import compiler/core/core
import compiler/core/corevar
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearmap
import newstd/data/linearset

// Re-analyze a recursive binding group just after type checking.
// Due to overloading, functions that seem mutually recursive may not
// actually be mutually recursive after the types are resolved.
alias deps = linearMap<tName, linearSet<tName>>
alias freeVar = linearSet<tName>

// Re-analyze a recursive binding group and return a list of new
// definition groups. After type checking it is possible that definitions
// that seemed recursive are actually not mutually recursive.

fun regroup(dfs: list<def>): <compFlags,pure> list<defGroup>
  match dfs
    Cons(d, Nil) ->
      val fvdef = d.freeVars
      //  this is for recursive definitions where the type may still differ since we cannot improve too early for mutual recursive definitions (or we unify too eagerly, see "while")
      if fvdef.member(TName(d.defName, d.ktype)) || 
        fvdef.list.map(getName).filter(fn(n) !n.isQualified).any(fn(dn) dn == d.defName) then
        [DefRec([d])]
      else
        [DefNonRec(d)]
    defs ->
      val defNames = defs.map(fn(d) TName(d.defName, d.ktype))
      val defNameSet = defNames.linearSet((==), show)
      val defMap = defNames.zip(defs)
      val deps = defNames.zip(defs.map(fn(d) d.freeVars.intersection(defNameSet)))
      // determine strongly connected components
      val defOrder = deps.map(fn((nm, fvs)) (nm, fvs.list)).scc((==), show)
      // create a definition group
      fun makeGroup(names)
        match names
          [nm] -> 
            if deps.find(nm).member(nm) then DefRec([defMap.find(nm)])
            else DefNonRec(defMap.find(nm))
          _ -> DefRec(names.map(fn(nm) defMap.find(nm)))
      defOrder.map(makeGroup)

fun find(nameMap: list<(tName, b)>, nm: tName): <compFlags,exn> b
  match std/core/find(nameMap, fn(n) n.fst == nm)
    Just(x) -> x.snd
    _ -> fail("core/binding-groups find: could not find: " ++ nm.show)



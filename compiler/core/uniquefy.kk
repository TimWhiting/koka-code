import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/core/corevar
import newstd/data/linearset
import newstd/data/linearmap

alias locals = nameSet;
alias renaming = name-map<name>

effect uniquefy
  fun setLocals(l: locals): ()
  fun getLocals(): locals
  fun setRenaming(r: renaming): ()
  fun getRenaming(): renaming

fun fullLocalized(f)
  val locals = getLocals()
  val r = localized(f)
  setLocals(locals)
  r

fun localized(f)
  val ren = getRenaming()
  val r = f()
  setRenaming(ren)
  r

fun runUn(start: int, f: () -> <uniquePhase,uniquefy|e> a): e a
  with runUniquePhase(start)
  with runUn()
  f()

val eqName = fn(n1: name, n2: name) n1 == n2
fun runUn(f: () -> <uniquePhase,uniquefy|e> a): <uniquePhase|e> a
  var locals := namesEmpty
  var renaming := linearMap([], eqName, eqName, show, show)
  with handler
    fun setLocals(l) locals := l
    fun getLocals() locals
    fun setRenaming(r) renaming := r
    fun getRenaming() renaming
  f()

fun uniquefy(e: expr): expr
  uniquefy(e, tnamesEmpty)

fun uniquefy(e: expr, free: linearSet<tName>): expr
  val locals = free.union(e.freeLocals).map(getName, eqName, show)
  with runUn(0)
  setLocals(locals)
  e.uniquefyExprX

fun uniquefyExprU(e: expr)
  with runUn()
  val e' = e.uniquefyExprX
  (e', getUnique())

fun uniquefy(c: core)
  c(defs=uniquefy(c.defs))

fun uniquefy(dgs: defGroups): defGroups
  // TOOD:







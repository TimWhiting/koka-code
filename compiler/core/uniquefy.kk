import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/core/corevar
import compiler/type/type
import std/data/linearset
import std/data/linearmap

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
  with run-unique(start)
  with runUn()
  f()

val eqName = fn(n1: name, n2: name) n1 == n2
fun fun/runUn(f: () -> <uniquePhase,uniquefy|e> a): <uniquePhase|e> a
  var locals := names/empty
  var renaming := LinearMap([])
  with handler
    fun setLocals(l) locals := l
    fun getLocals() locals
    fun setRenaming(r) renaming := r
    fun getRenaming() renaming
  f()

fun expr/uniquefy(e: expr): pure expr
  uniquefy(e, tnames/empty)

fun free/uniquefy(e: expr, free: linearSet<tName>): pure expr
  val locals = LinearSet(free.union(e.free-locals).list.map(get-name))
  with runUn(0)
  setLocals(locals)
  e.uniquefyExprX

fun uniquefyExprU(e: expr)
  with runUn()
  val e' = e.uniquefyExprX
  (e', get-unique())

fun uniquefy(c: core): pure core
  c(defs=uniquefy(c.defs))

fun dgs/uniquefy(dgs: defGroups): pure defGroups
  with runUn(0)
  val locals = getLocals()
  val topLevelDefs = dgs.flatten.map(def-name).filter(fn(n:name) !n.is-nil)
  setLocals(topLevelDefs.foldl(locals, fn(acc, n) acc.add(n.unqualify)))
  dgs.map(fn(dg) fullLocalized({uniquefyDG(dg)}))

fun dg/uniquefyDG(dg: defGroup)
  match dg
    DefNonRec(d) -> DefNonRec(d(defExpr=d.defExpr.uniquefyExprX))
    DefRec(ds) -> DefRec(ds.map(fn(d) d(defExpr=d.defExpr.uniquefyExprX)))

fun dg/uniquefy(dg: defGroup): pure defGroup
  with runUn(0)
  match dg
    DefNonRec(d) -> DefNonRec(d.uniquefyDef)
    DefRec(defs) ->
      val locals = getLocals()
      setLocals(defs.map(def-name).filter(fn(n) !n.is-nil).foldl(locals, fn(acc, n) acc.add(n)))
      DefRec(defs.map(fn(d) d(defExpr=localized({d.defExpr.uniquefyExprX}))))

fun uniquefyInnerDefGroup(dg: defGroup)
  match dg
    DefNonRec(d) -> DefNonRec(uniquefyDef(d))
    DefRec(defs) -> DefRec(uniquefyRecDefs(defs))

fun uniquefyRecDefs(defs: list<def>)
  val names = defs.map(fn(d) d.def-name.uniquefyName)
  val exprs = localized({defs.map(fn(d) d.defExpr.uniquefyExprX)})
  names.zip(exprs).zip(defs).map(fn(((n, e), d)) d(def-name=n, defExpr=e))

fun uniquefyDef(d: def)
  val expr1 = localized({d.defExpr.uniquefyExprX})
  val name1 = d.def-name.uniquefyName
  d(def-name=name1, defExpr=expr1)

fun uniquefyExprX(e: expr)
  match e
    Lam(tnames, eff, expr) ->
      with localized  
      val tnames1 = tnames.map(uniquefyTName)
      val expr1 = expr.uniquefyExprX
      Lam(tnames1, eff, expr1)
    Var(tname, info) ->
      val renaming = getRenaming()
      match renaming.lookup(tname.get-name)
        Just(nm) -> Var(TName(nm, tname.type-of), info)
        Nothing -> e
    App(f, args) -> App(f.uniquefyExprX, args.map(uniquefyExprX))
    TypeLam(tvs, expr) -> TypeLam(tvs, expr.uniquefyExprX)
    TypeApp(expr, tps) -> TypeApp(expr.uniquefyExprX, tps)
    Con -> e
    ELit -> e
    Let(defGroups, expr) -> Let(defGroups.map(uniquefyInnerDefGroup), expr.uniquefyExprX)
    Case(exprs, branches) ->
      Case(exprs.map(uniquefyExprX), localized({branches.map(fn(b) b.uniquefyBranch(exprs.map(type-of)))}))

fun uniquefyBranch(b: branch, patTps: list<ktype>)
  val patts = b.patterns.zip(patTps).map(fn((p, t)) p.uniquefyPattern(t))
  val guards = b.guards.map(uniquefyGuard)
  Branch(patts, guards)

fun uniquefyGuard(g: guard)
  Guard(g.test.uniquefyExprX, g.body.uniquefyExprX)

fun uniquefyPattern(pat: pattern, patTp: ktype)
  match pat
    PatVar(tname, p) -> PatVar(tname.uniquefyTName, p.uniquefyPatternX(patTp))
    _ ->
      val name = "pat".new-hidden-name.uniquefyName
      val p = pat.uniquefyPatternX(patTp)
      PatVar(TName(name, patTp), p)

fun uniquefyPatternX(p: pattern, patTp: ktype)
  match p
    PatWild -> p
    PatLit -> p
    PatCon(patName, pats, repr, typeArgs, kexists, typeRes, info, skip) ->
      PatCon(patName, pats.zip(typeArgs).map(fn((p', t)) p'.uniquefyPattern(t)), repr, typeArgs, kexists, typeRes, info, skip)
    PatVar(tname, pat) -> PatVar(tname.uniquefyTName, pat.uniquefyPatternX(patTp)) 

fun uniquefyTName(tn: tName)
  TName(tn.get-name.uniquefyName, tn.type-of)

fun makeFullUnique()
  get-unique() != 0

fun uniquefyName(n:name)
  if n.is-nil then n
  else
    val locals = getLocals()
    val full = makeFullUnique()
    if full || locals.member(n) then
      val renaming = getRenaming()
      val name1 = if full then n.unique-name-from else find-unique-name(0, n, locals)
      setLocals(locals.add(name1))
      setRenaming(renaming.add(n, name1))
      name1
    else 
      setLocals(locals.add(n))
      n

fun find-unique-name(i: int, n: name, locals: nameSet): div name
  val name1 = to-unique-name(i, n)
  if locals.member(name1) then find-unique-name(i+1, n, locals)
  else name1
import compiler/lib/pprint
import compiler/common/failure
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/kind/kind
import compiler/type/type
import compiler/type/kind
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/assumption
import compiler/core/core
import compiler/core/corevar
import compiler/platform/config
import newstd/data/linearset

fun liftFunctions()
  with handleFunLift()
  setCoreDefs(liftDefGroups(getCoreDefs(), True))

effect funLiftEffect
  fun emitLifted(dg: defGroup): ()
  fun emitLifteds(dgs: defGroups): ()
  fun collectLifted(): defGroups

effect currentDefEffect
  val currentDef: list<def>

alias liftDefEff = <funLiftEffect, currentDefEffect, pure, uniquePhase, comp-flags>

fun currentDefNames()
  currentDef.map(fn(d) d.def-name)

fun setCurrentDef(d: def, f)
  with override
    val currentDef = [d] ++ currentDef
  f()

fun handleFunLift(f)
  var lifted := []
  with handler
    fun emitLifted(dg) lifted := Cons(dg, lifted)
    fun emitLifteds(dgs) lifted := dgs ++ lifted
    fun collectLifted() 
      val l = lifted
      lifted := []
      l
  with handler
    val currentDef = []
  f()

// Transform definition groups
fun liftDefGroups(defgs: defGroups, topLevel: bool): liftDefEff defGroups
  defgs.map(fn(x) liftDefGroup(x, topLevel)).concat

fun substWithLiftedExpr(d: def, subst)
  val body = match d.defExpr
    TypeLam(tpars, Lam(pars, eff, lbody)) -> TypeLam(tpars, Lam(pars, eff, subst |-> lbody))
    Lam(pars, eff, lbody) -> Lam(pars, eff, subst |-> lbody)
    e -> fail("core/fun-lift liftDefGroup: expected lambda, got " ++ e.show)
  // Note here we only want to skip the substitution for fvs and tvs,
  // but we have skipped more than necessary, i.e.,
  // the part of those tpars and pars that are not in fvs and tvs.
  // But it is OK here, because fvs/tvs are in the scope on all defs,
  // and we have ensured that fvs/pars and tvs/tpars are always unique (see type/infer)
  d(defExpr = body)

fun liftDefGroup(defg: defGroup, topLevel: bool)
  if topLevel then
    match defg
      DefNonRec(d) ->
        val d' = d.liftDef(True)
        // all lifteddefinitions are put before the current definition
        collectLifted() ++ [DefNonRec(d')] 
      DefRec(defs) ->
        val defs' = defs.map(fn(d) d.liftDef(True))
        val lifted = collectLifted()
        // defs' depend on the lifted, but the lifted might depend on defs'
        // we could do a topological sort here (as in static/binding-groups) but for simplicity
        // we approximate here for now
        // Note that it can be important to have precise DefRec groups for other optimizations, like TMRC (compiler/core/ctail)
        val dnames = defs'.defsTNames
        val (gnonrecs, grecs) = lifted.partition(fn(dg) dg.freeVars.intersection(tnamesEmpty + dnames).is-empty)
        (gnonrecs ++ [DefRec(grecs.flatten ++ defs')])
  else
    match defg
      DefNonRec(d) -> [DefNonRec(d.liftDef(False))]
      DefRec(defs) ->
        val pinfoss = defs.map(paramInfos)
        val exprDocs = defs.map(fn(d) (d.defExpr, d.doc))
        val exprs = defs.map(fn(d) d.defExpr)
        val names = defs.map(defTName)
        val fvs = exprs.map(freeLocals).unions - names
        val tvs = exprs.map(free-type-vars).unions
        val (callExprs, liftedDefs0) = pinfoss.zip(names.zip(exprDocs)).map(fn((infos, (name, doc))) makeDef(fvs.list, tvs.list, infos, name, doc)).unzip
        val subst = names.zip(callExprs)
        val liftedDefs = liftedDefs0.map(fn(d) d.substWithLiftedExpr(subst))
        val groups = DefRec(liftedDefs).liftDefGroup(True) // lift all recs to top-level
        emitLifteds(groups)
        val defs' = defs.zipwith(callExprs, fn(d, c) d(defExpr = c, sort=d.sort.liftSort(False)))
        defs'.map(DefNonRec) // change a DefRec to all DefNonRecs

fun liftDef(d: def, topLevel: bool)
  with setCurrentDef(d)
  val expr' = d.defExpr.liftExpr(topLevel)
  d(defExpr=expr', sort=d.sort.liftSort(topLevel))

fun liftSort(s: defSort, b: bool)
  match (s, b)
    (DefFun, False) -> DefVal
    _ -> s

fun liftExpr(ex: expr, topLevel: bool)
  match ex
    App(f, args) -> App(f.liftExpr(False), args.map(fn(a) a.liftExpr(False)))
    Lam(args, eff, body) -> // don't lift anonymous functions
      Lam(args, eff, body.liftExpr(False))
    Let(defgs, body) ->
      Let(defgs.liftDefGroups(False), body.liftExpr(False))
    Case(exprs, bs) -> Case(exprs.map(fn(e) e.liftExpr(False)), bs.map(liftBranch))
    TypeLam(tvars, body) -> TypeLam(tvars, body.liftExpr(topLevel))
    TypeApp(body, targs) -> TypeApp(body.liftExpr(topLevel), targs)
    _ -> ex

fun liftBranch(Branch(pat, guards): branch)
  Branch(pat, guards.map(liftGuard))

fun liftGuard(Guard(test, expr): guard)
  Guard(test.liftExpr(False), expr.liftExpr(False))

fun makeDef(fvs: list<tName>, tvs: list<typeVar>, pinfos: list<paramInfo>, origName: tName, (expr, doc): (expr, string))
  val dnames = currentDefNames()
  val (name, inl) = uniqueNameCurrentDef()
  fun unwild(TName(nm, tp): tName)
    TName(if nm.nameId.head-char.unjust == '_' then prepend("wild", name) else name, tp) 
  val (tpars, pars, eff, body) = match expr
    TypeLam(tpars, Lam(pars, eff, lbody)) -> (tpars, pars.map(unwild), eff, lbody)
    Lam(pars, eff, lbody) -> ([], pars.map(unwild), eff, lbody)
    _ -> fail("core/fun-lift makeDef: expected lambda, got " ++ expr.show)
  val alltpars = tvs ++ tpars
  val allpars = fvs ++ pars
  val allargs = allpars.map(fn(t) Var(t, InfoNone))
  val allpinfos = fvs.map(fn(_) Own) ++ pinfos
  val liftedFun = addTypeLambdas(alltpars, Lam(allpars, eff, body))
  val liftedTp = liftedFun.typeOf
  val funExpr = Var(TName(name, liftedTp), InfoArity(alltpars.length, allargs.length))
  val etaExpr = match (tvs, fvs)
    (Nil, Nil) -> funExpr
    _ -> addTypeLambdas(tpars, Lam(pars, eff, App(addTypeApps(alltpars, funExpr), allargs)))
  val liftedDef = Def(name, liftedTp, liftedFun, Private, defFun(allpinfos), inl, rangeNull, "// lifted local: " ++ (dnames ++ [origName.getName]).map(fn(dn) dn.unqualify.show).join(", ") ++ "\n" ++ doc)
  (etaExpr, liftedDef)

fun uniqueNameCurrentDef()
  val current = currentDef.last.unjust
  val i = newUnique()
  val udef-name = toHiddenUniqueName(i,"lift",current.def-name)
  (udef-name, current.kinline)

// Don't lift a simple function. A function is simple if it's body is simply an
// application consisting of simple arguments.
// More general than eta-expanded expressions.
fun isSimpleFun(ex: expr)
  // The definition of simple arguments can be extended.
  fun isSimpleTArg(t: ktype)
    match t
      TCon -> True
      TVar -> True
      TApp(ty, tys) -> isSimpleTArg(ty) && tys.all(isSimpleTArg)
      _ -> False
  fun isSimpleArg(a: expr)
    match a
      Con -> True
      ELit -> True
      Var -> True
      App(e, es) -> isSimpleArg(e) && es.all(isSimpleArg)
      _ -> False
  match ex
    Lam(_, _, App(_, args)) -> args.all(isSimpleArg)
    TypeLam(_, Lam(_, _, App(TypeApp(_, targs), args))) ->
      targs.all(isSimpleTArg) && args.all(isSimpleArg)
    TypeLam(_, Lam(_, _, App(_, args))) -> args.all(isSimpleArg)
  

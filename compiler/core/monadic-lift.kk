import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/syntax
import compiler/type/type
import compiler/kind/kind
import compiler/core/core
import compiler/core/corevar
import compiler/type/typevar
import std/data/linearset
import compiler/platform/config

fun monadicLift()
  with runLifted()
  setCoreDefs(getCoreDefs().liftDefGroups(True))

//   transform definition groups
fun liftDefGroups(dgs: defGroups, topLevel: bool)
  dgs.map(fn(dg) dg.liftDefGroup(topLevel)).concat

alias liftedEff = <lifted, uniquePhase, pure, comp-flags>
effect lifted
  fun emit(dg: defGroup): ()
  fun collect(): list<defGroup>
  val currentDef: list<def>

fun runLifted(f: () -> <lifted|e> a): e a 
  var dgs := []
  with handler
    fun emit(dg) 
      dgs := Cons(dg, dgs)
    fun collect() 
      val dgs' = dgs
      dgs := []
      dgs'
    val currentDef = Nil
  mask<local>{f()}

// transform definition groups
fun liftDefGroup(dg: defGroup, topLevel: bool)
  if topLevel then
    match dg
      DefNonRec(d) ->
        val d' = d.liftDef(topLevel)
        collect() ++ [DefNonRec(d')]
      DefRec(ds) ->
        val ds' = ds.map(fn(d) d.liftDef(topLevel))
        collect() ++ [DefRec(ds')]
  else
    match dg
      DefNonRec(d) -> [DefNonRec(d.liftDef(topLevel))]
      DefRec(ds) -> [DefRec(ds.map(fn(d) d.liftDef(topLevel)))]
  
fun liftDef(d: def, topLevel: bool)
  with override
    val currentDef = Cons(d, currentDef)
    fun emit(dg) emit(dg)
    fun collect() collect()
  val expr' = if topLevel then d.defExpr.liftExprInl(topLevel).snd else d.defExpr.liftExpr(topLevel)
  d(defExpr = expr')

// Transform expressions

fun liftExprInl(expr': expr, topLevel: bool): liftedEff (expr, expr)
  match expr'
    App(tpapp as TypeApp(Var(TName(nameB)), [tpArg, tpRes, tpEff]), [bexpr, Lam([arg], eff, body)]) | nameB == nameBind ->
      val (body', ibody') = body.liftExprInl(False)
      val bexpr' = bexpr.liftExpr(False)
      val f = Lam([arg], eff, body').liftLocalFun(typeTotal)
      val bind = App(tpapp, [bexpr', f])
      val a = TypeVar(0, kindStar, Bound)
      val b = TypeVar(1, kindStar, Bound)
      val e = TypeVar(2, kindEffect, Bound)
      val typeBind2 = TForAll([a, b, e], [], 
        TFun([(nil, TVar(a)), 
                 (nil, TFun([(nil, TVar(a))], TVar(e), TVar(b))),
                 (nil, TFun([(nil, TVar(a))], TVar(e), TVar(b))),
                 ], TVar(e), TVar(b)))
      val ibind = App(TypeApp(Var(TName(nameBind2, typeBind2), InfoArity(3, 3)), [tpArg, tpRes, tpEff]), [bexpr', f, (Lam([arg], eff, ibody'))])
      (bind, ibind)
    Let(defgs, body) ->
      val defgs' = defgs.liftDefGroups(False)
      val (body', ibody') = body.liftExprInl(False)
      (Let(defgs', body'), Let(defgs', ibody'))
    Case(exprs, bs) ->
      val exprs' = exprs.map(fn(e) e.liftExpr(False))
      val (bs', ibs') = bs.map(liftBranchInl).unzip
      (Case(exprs', bs'), Case(exprs', ibs'))
    TypeLam(tvars, body) ->
      val (body', ibody') = body.liftExprInl(topLevel)
      (TypeLam(tvars, body'), TypeLam(tvars, ibody'))
    TypeApp(body, tps) ->
      val (body', ibody') = body.liftExprInl(topLevel)
      (TypeApp(body', tps), TypeApp(ibody', tps))
    Lam(args, eff, body) ->
      val (body', ibody') = body.liftExprInl(False)
      (Lam(args, eff, body'), Lam(args, eff, ibody'))
    _ ->
      val newE = expr'.liftExpr(topLevel)
      (newE, newE)

fun liftBranchInl(Branch(pat, guards): branch): liftedEff (branch, branch)
  val (guards', iguards') = guards.map(liftGuardInl).unzip
  (Branch(pat, guards'), Branch(pat, iguards'))

fun liftGuardInl(Guard(guard, body): guard)
  val guard' = guard.liftExpr(False)
  val (body', ibody') = body.liftExprInl(False)
  (Guard(guard', body'), Guard(guard', ibody'))

fun liftExpr(expr': expr, topLevel: bool): liftedEff expr
  match expr'
    App(tpApp as TypeApp(Var(TName(nameB))), [bexpr, Lam([arg], eff, body)]) | nameB == nameBind ->
      val body' = body.liftExpr(False)
      val bexpr' = bexpr.liftExpr(False)
      val f = Lam([arg], eff, body').liftLocalFun(typeTotal)
      App(tpApp, [bexpr', f])
    App(f, args) ->
      val f' = f.liftExpr(False)
      val args' = args.map(fn(e) e.liftExpr(False))
      App(f', args')
    Lam(args, eff, body) ->
      val body' = body.liftExpr(False)
      Lam(args, eff, body')
    Let(defgs, body) ->
      val defgs' = defgs.liftDefGroups(False)
      val body' = body.liftExpr(False)
      Let(defgs', body')
    Case(exprs, bs) ->
      val exprs' = exprs.map(fn(e) e.liftExpr(False))
      val bs' = bs.map(liftBranch)
      Case(exprs', bs')
    TypeLam(tvars, body) ->
      val body' = body.liftExpr(topLevel)
      TypeLam(tvars, body')
    TypeApp(body, tps) ->
      val body' = body.liftExpr(topLevel)
      TypeApp(body', tps)
    _ -> expr'

fun liftLocalFun(e: expr, eff: keffect)
  val fvs = e.free-locals.list
  val tvs = e.free-type-vars.list
  val (expr2, liftDef) = e.makeDef(fvs, tvs)
  emit(DefNonRec(liftDef))
  expr2

fun makeDef(e: expr, fvs: list<tName>, tvs: list<typeVar>)
    
  fun unwild(TName(name, tp): tName)
    TName(if name.nameStem == "" || name.nameStem.starts-with("_").is-just then prepend("wild", name) else name, tp)
  val (tpars, pars, eff, body) = match e
    TypeLam(tpars, Lam(pars, eff, lbody)) -> (tpars, pars.map(unwild), eff, lbody)
    Lam(pars, eff, lbody) -> ([], pars.map(unwild), eff, lbody)
    _ -> fail("core/monadic-lift makeDef lifting non function? " ++ e.show)
  val alltpars = tvs ++ tpars
  val allpars = fvs ++ pars
  val allargs = allpars.map(fn(tn) Var(tn, InfoNone))
  val liftedFun = addTypeLambdas(alltpars, Lam(allpars, eff, body))
  val liftedTp = liftedFun.type-of
  fun liftedDef(nm, inl)
    Def(nm, liftedTp, liftedFun, Private, DefFun([]), InlineAuto, range/null, "// monadic lift")
  fun funExpr(n: name)
    Var(TName(n, liftedTp), InfoArity(alltpars.length, allargs.length))
  fun etaExpr(n: name)
    match (tvs, fvs)
      (Nil, Nil) -> n.funExpr
      _ -> addTypeLambdas(tpars, Lam(pars, eff, App(addTypeApps(alltpars, funExpr(n)), allargs)))
  val (name, inl) = uniqueNameCurrentDef()
  (name.etaExpr, name.liftedDef(inl))
  
// branches
fun liftBranch(Branch(pat, guards): branch)
  val guards' = guards.map(liftGuard)
  Branch(pat, guards')

fun liftGuard(Guard(guard, body): guard)
  val guard' = guard.liftExpr(False)
  val body' = body.liftExpr(False)
  Guard(guard', body')

fun uniqueNameCurrentDef()
  val d = currentDef.last.unjust
  val i = new-unique()
  val udef-name = to-hidden-unique-name(i, "mlift", d.def-name)
  (udef-name, d.kinline)
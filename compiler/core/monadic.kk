import compiler/core/core
import compiler/type/assumption
import compiler/core/corevar
import compiler/type/type
import compiler/type/typevar
import compiler/kind/kind
import compiler/common/syntax
import compiler/common/failure
import compiler/common/name-prim
import compiler/common/name
import compiler/common/range
import compiler/platform/config

alias monadicEff = <comp-flags,monadic,uniquePhase,pure>

effect monadic
  val currentDef: list<def>
  val isInBind: bool

fun runMon(f)
  handle(f)
    val currentDef = Nil
    val isInBind = False

fun monTransform()
  with runMon()
  setCoreDefs(monDefGroups(getCoreDefs()))

// tansform definition groups
fun monDefGroups(dgs: defGroups)
  dgs.map(monDefGroup)

fun monDefGroup(dg): monadicEff defGroup
  match dg
    DefRec(defs) -> DefRec(defs.map(fn(d) d.monDef(True)))
    DefNonRec(d) -> DefNonRec(d.monDef(False))

fun setCurrentDef(d, f)
  with override
    val currentDef = Cons(d, currentDef)
    val isInBind = isInBind
  f()

// transform a definition
fun monDef(d: def, isRecursive: bool)
  if !d.isMonDef then
    d
  else
    with setCurrentDef(d)
    d(defExpr = d.defExpr.monExpr(True)(id))

alias trans<a> = transX<a, a>
alias transX<a, b> = (a -> monadicEff b) -> monadicEff b

fun monExpr(e: expr): monadicEff trans<expr>
  e.monExpr(False)

fun monExpr(expr: expr, topLevel: bool): monadicEff trans<expr>
  match expr
    // Optimized open binding
    // note: we cannot just check for `effFrom.isMonEffect` as the effFrom
    // might be total but inside we may still need a monadic translation if `f`
    // constains handlers itself for example
    App(App(eopen as TypeApp(Var(open), [_, _, _, _]), [f]), args) | open.getName == nameEffectOpen && !f.isMonExpr ->
      val args' = args.map(monExpr)
      fn(k) applies(args', fn(argss) k(App(App(eopen, [f]), argss)))
    App(TypeApp(App(eopen as TypeApp(Var(open), [_, _, _, _]), [f]), targs), args) | open.getName == nameEffectOpen && !f.isMonExpr ->
      val args' = args.map(monExpr)
      fn(k) applies(args', fn(argss) k(App(TypeApp(App(eopen, [f]), targs), argss)))
    // lift open applications
    App(eopen as TypeApp(Var(open), [_, _, _, _]), [f]) | open.getName == nameEffectOpen ->
      val f' = f.monExpr
      fn(k) f'(fn(ff) k(App(eopen, [ff])))
    // regular cases
    Lam(args, eff, body) ->
      val body' = body.monExpr
      fn(k) k(Lam(args, eff, body'(id)))
    App(f, args) ->
      val f' = f.monExpr
      val args' = args.map(monExpr)
      val ftp = f.typeOf
      val feff =
        val (_, _, rho) = ftp.splitPredType
        match rho.splitFunType
          Just((_, feff, _)) -> feff
          _ -> fail("core/monadic app: illegal application")
      if (f.isNeverMon || !(ftp.isMonType || f.isAlwaysMon)) then
        fn(k) f'(fn(ff) applies(args', fn(argss) k(App(ff, argss))))
      else
        val namey = "y".uniqueName
        fn(k)
          val resTp = expr.typeOf
          val tnamey = TName(namey, resTp)
          val contBody = k(Var(tnamey, InfoNone))
          val cont = match contBody
            // optimize (fun (y) {lex x = y in ..})
            Let([DefNonRec(d as Def(defExpr=Var(v)))], body) | v.getName == namey ->
              Lam([TName(d.defName, d.ktype)], feff, body)
            // TODO: optimize (fun (y) {lift(expr)})?
            body -> Lam([tnamey], feff, body)
          f'(fn(ff) applies(args', fn(argss) appBind(resTp, feff, contBody.typeOf, ff, argss, cont)))
    Let(defgs, body) ->
      defgs.monLetGroups(body)
    Case(exprs, bs) ->
      val exprs' = monTrans(monExpr, exprs)
      val bs' = bs.map(monBranch)
      if !bs.any(isMonBranch) then
        fn(k) exprs'(fn(xss) k(Case(xss, bs')))
      else
        val nameC = "c".uniqueName
        val resTp = expr.typeOf
        val tnameC = TName(nameC, resTp)
        fn(k)
          val effTp = typeTotal
          val contBody = k(Var(tnameC, InfoNone))
          val cont = Lam([tnameC], effTp, contBody)
          exprs'(fn(xss) applyBind(resTp, effTp, contBody.typeOf, Case(xss, bs'), cont))
    v as Var ->
      fn(k) k(v)
    // type application and abstraction
    TypeLam(tvars, body) ->
      val body' = body.monExpr(topLevel)
      fn(k) body'(fn(xx) k(TypeLam(tvars, xx)))
    TypeApp(body, tps) ->
      val body' = body.monExpr(topLevel)
      fn(k) body'(fn(xx) k(TypeApp(xx, tps)))
    _ -> fn(k) k(expr)

fun monBranch(Branch(pat, guards): branch)
  Branch(pat, guards.map(monGuard))

fun monGuard(Guard(guards, body): guard)
  Guard(guards, (body.monExpr)(id)) // guards are total!

fun monLetGroups(dgs: defGroups, body: expr)
  match dgs
    Nil -> body.monExpr
    Cons(dg, dgs') ->
      val dg' = dg.monLetGroup
      val expr' = dgs'.monLetGroups(body)
      fn(k) dg'(fn(xdg) Let(xdg, expr'(k)))

fun monLetGroup(dg: defGroup)
  match dg
    DefRec(defs) ->
      val ldefs = monTrans(fn(d) monLetDef(True, d), defs)
      fn(k) ldefs(fn(xss) k(xss.map(fn((xds, yds, nds)) ([DefRec(xds)] ++ (if yds.is-nil then [] else [DefRec(yds)]) ++ nds.map(DefNonRec))).concat))
    DefNonRec(d) ->
      val ldef = monLetDef(False, d)
      fn(k) ldef(fn((xds, yds, nds)) k([xds,yds,nds].concat.map(DefNonRec)))

fun monLetDef(isRec: bool, d: def): monadicEff transX<(list<def>, list<def>, list<def>), expr>
  with setCurrentDef(d)
  val expr' = d.defExpr.monExpr(True)
  fn(k) expr'(fn(xx:expr) k(([d(defExpr=xx)], [], [])))

fun monTrans(f: (a -> monadicEff transX<b, c>), xs: list<a>): monadicEff transX<list<b>,c>
  match xs
    Nil -> fn(k) k([])
    Cons(x, xx) ->
      val x' = f(x)
      val xx' = monTrans(f, xx)
      fn(k) x'(fn(y) xx'(fn(ys) k(Cons(y, ys))))

fun applies(l: list<trans<a>>, f: (list<a>) -> monadicEff a): monadicEff a
  match l
    Nil -> f([])
    Cons(x, xx) -> x(fn(y) applies(xx, fn(ys) f(Cons(y, ys))))

fun appBind(tpArg, tpEff, tpRes, f, args, cont)
  applyBind(tpArg, tpEff, tpRes, App(f, args), cont)

fun applyBind(tpArg, tpEff, tpRes, expr, cont)
  match cont
    Lam([aname], _, Var(v)) | v.getName == aname.getName -> expr
    _ -> monMakeBind(tpArg, tpEff, tpRes, expr, cont)

fun monMakeBind(tpArg, tpEff, tpRes, arg, next)
  App(TypeApp(Var(TName(nameBind, typeBind), InfoArity(2, 3)), [tpArg, tpRes, tpEff]), [arg, next])

val typeBind = TForAll([tvarA, tvarB, tvarE], [], 
    TFun([
      (nameNil, typeYld(TVar(tvarA))), 
      (nameNil, TFun([(nameNil, TVar(tvarA))], TVar(tvarE), typeYld(TVar(tvarB))))], TVar(tvarE), typeYld(TVar(tvarB))))

fun typeYld(tp: ktype) 
  tp // TSyn(TypeSyn(nameTypeYld, kindFun(kindStar, kindStar), 0, Nothing), [tp], tp)

val tvarA = TypeVar(0, kindStar, Bound)
val tvarB = TypeVar(1, kindStar, Bound)
val tvarE = TypeVar(2, kindEffect, Bound)

// Check if expressions need monadic translation

// Some expressions always need mon translation
fun isAlwaysMon(e: expr)
  match e
    TypeApp(e') -> e'.isAlwaysMon
    Var(v) -> v.getName == nameUnsafeTotal // TODO: remove these special cases (previously also included nameYieldOp && namePerform(0))
    _ -> False

// Some expressions never need mon translation
fun isNeverMon(e: expr)
  match e
    App(TypeApp(Var(open), [effFrom, _, _, _]), [_]) | open.getName == nameEffectOpen ->
      effFrom.isTypeTotal // TODO: more cases? generally handler free
    TypeApp(e') -> e'.isNeverMon
    Var(v) -> v.getName == canonicalName(1, nameDeref) // TODO: remove special case?
    _ -> e.isTotal

// Does this definition need any mon translation (sometimes deeper inside)
fun isMonDef(d: def)
  d.defExpr.isMonExpr' || d.ktype.isMonType

fun isMonExpr(e: expr): bool
  unsafe-total
    unsafe-no-div
      e.isMonExpr'

fun isMonExpr'(e: expr)
  match e
    App(TypeApp(Var(open), [_, effTo]), [f]) | open.getName == nameEffectOpen ->
      effTo.isMonEffect || f.isMonExpr'
    App(f, args) -> Cons(f, args).any(isMonExpr')
    Lam(_, eff, body) -> eff.isMonEffect || body.isMonExpr'
    TypeApp(TypeLam(_, body), targs) -> targs.any(isMonType) || body.isMonExpr'
    TypeApp(Var, targs) -> targs.any(isMonType) || e.typeOf.isMonType
    TypeApp(body, targs) -> targs.any(isMonType) || body.isMonExpr'
    TypeLam(_, body) -> body.isMonExpr'
    Let(defs, body) -> defs.any(isMonDefGroup) || body.isMonExpr'
    Case(exprs, bs) -> exprs.any(isMonExpr') || bs.any(isMonBranch)
    _ -> e.typeOf.isMonType

fun isMonDefGroup(dg: defGroup)
  match dg
    DefRec(defs) -> defs.any(isMonDef)
    DefNonRec(d) -> isMonDef(d)

fun isMonBranch(Branch(_, guards): branch)
  guards.any(isMonGuard)

fun isMonGuard(Guard(g, e): guard)
  g.isMonExpr' || e.isMonExpr'


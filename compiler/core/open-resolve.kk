import compiler/common/name
import compiler/common/range
import compiler/common/name-prim
import compiler/common/failure
import compiler/platform/config
import compiler/common/syntax
import compiler/core/core
import compiler/core/corevar
import compiler/type/assumption
import compiler/type/type
import compiler/type/pretty
import compiler/type/kind
import compiler/kind/kind
import compiler/lib/pprint

alias openEff = <openEffect, comp-flags, uniquePhase, pure, documentation>

effect openEffect
  fun getGamma(): gamma

fun openResolve()
  setCoreDefs(resDefGroups(getCoreDefs()))

// transform definition groups
fun resDefGroups(dgs: defGroups): openEff defGroups
  dgs.map(resDefGroup)

fun resDefGroup(dg: defGroup): openEff defGroup
  match dg
    DefRec(dfs) -> DefRec(dfs.map(resDef))
    DefNonRec(df) -> DefNonRec(resDef(df))

// Transform a definition
fun resDef(d: def)
  d(defExpr=d.defExpr.resExpr)

fun resExpr(ex: expr)
  match ex
    App(eopen as TypeApp(Var(open), [effFrom, effTo, tpFrom, tpTo]), [f]) | open.getName == nameEffectOpen ->
      resOpen(eopen, effFrom, effTo, tpFrom, tpTo, resExpr(f))
    // regular cases
    Lam(args, eff, body) -> Lam(args, eff, body.resExpr)
    App(f, args) -> App(f.resExpr, args.map(resExpr))
    Let(dfgs, body) -> Let(dfgs.resDefGroups, body.resExpr)
    Case(exprs, bs) -> Case(exprs.map(resExpr), bs.map(resBranch))
    TypeLam(tvars, body) -> TypeLam(tvars, body.resExpr)
    TypeApp(f, tps) -> TypeApp(f.resExpr, tps)
    _ -> ex // var,lit

fun resBranch(Branch(pat, guards): branch)
  Branch(pat, guards.map(resGuard))

fun resGuard(Guard(test, body): guard)
  Guard(test.resExpr, body.resExpr)

// Insert open call
fun resOpen(eopen: expr, effFrom: ktype, effTo: ktype, tpFrom: ktype, tpTo: ktype, expr: expr)
  match tpTo
    TFun(targs, _, tres) ->
      val n = targs.length
      val (lsFrom, tlFrom) = effFrom.extractHandledEffect
      val (lsTo, tlTo) = effTo.extractHandledEffect
      if effFrom == effTo then
        // exact match just use expr
        expr
      elif !effFrom.isEffectFixed then
        fail("core/open-resolve resOpen: todo: masking handled effect " ++ effFrom.pretty.show)
      elif tlFrom.matchType(tlTo) && lsFrom.length == lsTo.length && lsFrom.zip(lsTo).all(fn((t1, t2)) t1 == t2) then
        // same handled effects, just use expr
        expr
      else
        // not equal in handled effects, insert open
        fun resolve(nm: name)
          match getGamma().gammaLookup(nm)
            [(qname, info)] -> info.coreExpr(qname)
            _ -> fail("core/open-resolve resOpen: unknown name: " ++ nm.show)
        val params = list(1, targs.length).zip(targs).map(fn((i, t)) TName(newHiddenName("x" ++ i.show), t.snd))
        val exprName = TName(newHiddenName("x0"), tpFrom)
        val exprVar = Var(exprName, InfoNone)
        fun exprApp(lam: expr)
          App(Lam([exprName], typeTotal, lam), [expr])
        fun wrapperThunk(openExpr: expr, evExprs: list<expr>)
          exprApp(Lam(params, effTo, 
            App(TypeApp(openExpr, [tres, effFrom, effTo]), 
              evExprs ++ [Lam([], effTo, App(exprVar, params.map(fn(p) Var(p, InfoNone))))])))
        fun wrapper(openExpr: expr, evExprs: list<expr>)
          exprApp(Lam(params, effTo, 
            App(TypeApp(openExpr, targs.map(snd) ++ [tres, effFrom, effTo]), 
              evExprs ++ [exprVar] ++ params.map(fn(p) Var(p, InfoNone)))))
        fun evIndexOf(l: ktype)
          val (htagTp, hndTp) = 
            val (name, _, tpArgs) = l.labelNameEx
            val hndCon = TCon(TypeCon(name.toHandlerName, kindFunN(tpArgs.map(kind) ++ [kindEffect, kindStar], kindStar)))
            (makeTypeApp(resolve(name.toEffectTagName), tpArgs), TApp(hndCon, tpArgs))
          App(TypeApp(resolve(nameEvvIndex), [effTo, hndTp]), [htagTp])
        match lsFrom
          Nil -> // no handled effect, use cast
            match lsTo
              Nil -> expr
              _ -> 
                if expr.isHandlerFree then expr // fully total with using any operations that need evidence; just leave it as is
                elif n <= 4 then wrapper(resolve(n.nameOpenNone), []) // fails in perf1c with exceeded stack size if --optmaxdup < 500 (since it prevents a tailcall)
                else 
                  // expr -- fails in nim as it's evidence is not cleared
                  wrapperThunk(resolve(0.nameOpenNone), []) 
          [l] -> // just one: use open-atN for efficiency
            if n <= 4 then wrapper(resolve(nameOpenAt(n)), [l.evIndexOf])
            else wrapperThunk(resolve(nameOpenAt(0)), [l.evIndexOf])
          _ ->
            val indices = makeVector(typeEvIndex, lsFrom.map(evIndexOf))
            if n <= 3 then
              wrapper(resolve(n.nameOpen), [indices])
            else
              wrapperThunk(resolve(0.nameOpen), [indices])
    _ -> fail("core/open-resolve resOpen: open applied to a non-function? " ++ effTo.pretty.show)

// is a function expression handler free?: meaning if invoked it will never need evidence (invoke an operation) or change the eveidence (use a handler)
fun isHandlerFree(ex: expr)
  match ex
    TypeLam(_, body) -> isHandlerFree(body)
    TypeApp(f, _) -> isHandlerFree(f)
    Lam(_, eff, body) -> !containsHandledEffect([], eff) && isHandlerFree(body)
    App(f, args) -> isHandlerFree(f) && args.all(isHandlerFree)
    Var(vname, core/InfoExternal) -> 
      match vname.typeOf.handlerFreeFunType
        Nothing -> True
        Just(ok) -> ok
    Var(vname) ->
      match vname.typeOf.handlerFreeFunType
        Nothing -> True
        Just(ok) -> ok && vname.getName.isSystemCoreName
    Con -> True
    ELit -> True
    _ -> False

fun handlerFreeFunType(tp: ktype)
  match tp.splitFunScheme
    Just((_, _, _, eff, _)) -> Just(!containsHandledEffect([], eff))
    _ -> Nothing
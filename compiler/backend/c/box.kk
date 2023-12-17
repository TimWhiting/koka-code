import compiler/core/core
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/lib/pprint
import compiler/common/syntax
import compiler/type/type
import compiler/type/kind
import compiler/type/pretty
import compiler/kind/kind
import compiler/common/failure
import compiler/platform/config
import compiler/common/color-scheme

// Box / unbox transformation
alias boxEff = <uniquePhase,compFlags,documentation,pure,colorSchemeEffect,ppEnvEff>

fun boxCore(c: core): boxEff core
  c(defs=boxDefGroups(c.defs))

fun boxDefGroups(dgs: defGroups)
  dgs.map(boxDefGroup)

fun boxDefGroup(dg: defGroup)
  match dg
    DefRec(defs) -> DefRec(defs.map(boxDef))
    DefNonRec(d) -> DefNonRec(boxDef(d))

fun boxDef(d: def): boxEff def
  val bexpr = boxExpr(boxType(d.ktype), d.defExpr)
  val bdef = d(defExpr = bexpr)
  // simplify the whole def to avoid simplifying away functions to values (e.g. `fun(x){g(x)} -> val f = g`)
  bdef.uniqueSimplify(True, False, 3, 6)

// add box/unbox such that the type of `expr` matches `BoxType`
fun boxExpr(tp: ktype, ex: expr)
  match ex
    // remove type abstraction and applications
    TypeLam(_, e) -> boxExpr(tp, e)
    TypeApp(e, _) -> boxExpr(tp, e)
    // Regular
    App(e, args) ->
      val argTps = args.map(boxTypeOf)
      val eTp = TFun(argTps.map(fn(t) (nameNil, t)), typeTotal, tp)
      val bargs = args.map(fn(a) boxExpr(boxTypeOf(a), a))
      val be = boxExpr(eTp, e)
      App(be, bargs)
    Lam(tparams, eff, body) ->
      val fnTp = ex.boxTypeOf
      val bbody = boxExpr(tp, body)
      bcoerce(fnTp, tp, Lam(tparams, eff, bbody))
    Let(defGroups, body) ->
      val bdgs = defGroups.boxDefGroups
      val bbody = boxExpr(tp, body)
      Let(bdgs, bbody)
    Case(exprs, branches) ->
      val exprTps = exprs.map(boxTypeOf)
      val bexprs = exprTps.zip(exprs).map(fn((tp', e)) boxExpr(tp', e))
      val bbranches = branches.map(fn(b) boxBranch(exprTps, tp, b))
      Case(bexprs, bbranches)
    _ -> bcoerce(ex.boxTypeOf, tp, ex)

fun boxBranch(patTps: list<ktype>, tp: ktype, b: branch)
  val (bpatterns, defss) = patTps.zip(b.patterns).map(fn((pt, p)) boxPattern(pt, p)).unzip
  fun binds(ex: expr)
    makeLet(defss.concat.map(fn(d) DefNonRec(d)), ex)
  val bguards = b.guards.map(fn(g) boxGuard(tp, binds, g))
  Branch(bpatterns, bguards)

fun boxGuard(tp: ktype, binds: expr -> pure expr, Guard(test, expr): guard)
  val btest = boxExpr(typeBool, test)
  val bexpr = binds(boxExpr(tp, expr))
  Guard(btest, bexpr) // TODO: binds come to late to appear in guards but we need binds for function wrappers?.. perhaps create a special pattern just for the C backend?

// add bindings and box/unbox such that pattern matches the required boxtype
fun boxPattern(fromTp: ktype, p: pattern)
  if p.is-patWild then
    return boxPatternX(fromTp, p)
  val toTp = match p
    PatCon(typeRes=res) -> res
    PatVar(tname) -> tname.typeOf
    PatLit(l) -> l.typeOf
  if fromTp.cType != toTp.cType then
    val mcoerce = bcoerceX(fromTp, toTp, Var(TName(nameNil, fromTp), InfoNone))
    match mcoerce
      Just ->
        val isComplexCoerce =
          match (fromTp.cType, toTp.cType)
            (CFun, _) -> True
            (_, CFun) -> True
            _ -> False
        // We just insert a specially named Box pattern bound to fresh variable -- the backend recognizes this
        // and generates unbox/box expressions appropiately so nested patterns are handled correctly
        // Unfortunately, this does not work for function wrappers (as we need to generate a
        // wrapped unbox/box function around it); for those we rename and generate an explicit binding
        // binding; this works as a function type is never pattern matched further.
        // TODO: this may fail if the function is used in a guard test itself where it is not bound yet.
        //       we could work around this by substituting explicitly in the guard in that case.
        if isComplexCoerce then
          // function match
          match p
            PatVar(tname, PatWild) ->
              // ok, no nested match
              val i = newUnique()
              val uname = newHiddenName("fun-unbox-x" ++ i.show)
              val coerce = bcoerce(fromTp, toTp, Var(TName(uname, fromTp), InfoNone))
              val def = makeTDef(TName(tname.getName, toTp), coerce)
              (PatVar(TName(uname, fromTp), PatWild), [def])
            _ ->
              fail("backend/c/from-core boxPattern: nested match on a function?")
        else // regular box / unbox
          val i = newUnique()
          val uname = newHiddenName("box-x" ++ i.show)
          val (bpat, defs) = boxPatternX(toTp, p)
          (PatVar(TName(uname, typeBoxStar), patBox(toTp, typeBoxStar, bpat)), defs)
      _ ->
        boxPatternX(fromTp, p)
  else boxPatternX(fromTp, p)    

fun boxPatternX(fromTp: ktype, p: pattern)
  match p
    PatCon(name, pars, repr, targs, exists0, tres, conInfo, skip) ->
      val (bparams, defss) = conInfo.params.map(snd).zip(pars).map(fn((ftp, par)) boxPattern(ftp, par)).unzip
      (PatCon(name, bparams, repr, targs, exists0, tres, conInfo, skip), defss.concat)
    PatVar(tname, arg) ->
      val (barg, defs) = boxPattern(tname.typeOf, arg)
      (PatVar(tname, barg), defs)
    PatLit -> (p, [])
    PatWild -> (p, [])

// coerce `expr` of `fromTp` to `toTp`
fun bcoerce(fromTp: ktype, toTp: ktype, ex: expr)
  val mb = bcoerceX(fromTp, toTp, ex)
  match mb
    Just(e) -> e
    Nothing -> ex

fun bcoerceX(fromTp: ktype, toTp: ktype, ex: expr)
  val coerceTp = TFun([(nameNil, fromTp)], typeTotal, toTp)
  val boxVar = boxVarAtTp(coerceTp)
  val unboxVar = unboxVarAtTp(coerceTp)
  match (fromTp.cType, toTp.cType)
    (CBox, CBox) -> Nothing
    (CBox, CData) -> Just(App(unboxVar, [ex]))
    (CData, CBox) -> Just(App(boxVar, [ex]))
    // boxed functions need to be wrapped to take all arguments and results as boxed as well :-(
    // set test/cgen/box3 and test/cgen/box3a
    (CBox, CFun) ->
      val boxedToTp = toTp.boxedFunType
      val unboxed = App(unboxVarAtTp(TFun([(nameNil, fromTp)], typeTotal, boxedToTp)), [ex])
      Just(bcoerce(boxedToTp, toTp, unboxed)) // unwrap function; we must return Just even if no further wrapping was needed
    (CFun, CBox) ->
      val boxedFromTp = fromTp.boxedFunType
      val boxed = bcoerce(fromTp, boxedFromTp, ex) //wrap function
      val wrapped = App(boxVarAtTp(TFun([(nameNil, boxedFromTp)], typeTotal, toTp)), [boxed])
      Just(wrapped)
    // coerce between function arguments/results
    (CFun(fromPars, fromRes), CFun(toPars, toRes)) ->
      if !fromPars.zip(toPars).all(fn((t1, t2)) t1 == t2) && fromRes == toRes then
        match toTp.splitFunScheme
          Just((_, _, toParTps, toEffTp, toResTp)) ->
            match fromTp.splitFunScheme
              Just((_, _, fromParTps, fromEffTp, fromResTp)) -> Just(boxBindExprAsValue(fromTp, toTp, ex, fn(vexpr) boxCoerceFun(toParTps, toEffTp, toResTp, fromParTps, fromEffTp, fromResTp, vexpr)))
              _ -> fail("backend/c/box bcoerceX: expecting function (from): " ++ fromTp.pretty.show)
          _ -> fail("backend/c/box bcoerceX: expecting function (to): " ++ toTp.pretty.show)
      else Nothing
    _ -> Nothing

fun boxVarAtTp(tp: ktype)
  Var(TName(nameBox, tp), InfoExternal([(C(CDefault), "box(#1)")]))

fun unboxVarAtTp(tp: ktype)
  Var(TName(nameUnbox, tp), InfoExternal([(C(CDefault), "unbox(#1)")]))

fun boxCoerceFun(toParTps: list<(name, ktype)>, toEffTp: ktype, toResTp: ktype, fromParTps: list<(name, ktype)>, fromEffTp: ktype, fromResTp: ktype, ex: expr): <colorSchemeEffect,compFlags,pure,documentation,ppEnvEff,uniquePhase> expr
  val names = toParTps.map(fn(_) uniqueName("b"))
  val pars = names.zipwith(toParTps.map(snd), fn(n, t) TName(n,t))
  val args = pars.map(fn(p) Var(p, InfoNone))
  val bargs = zip3(args, toParTps.map(snd), fromParTps.map(snd)).map(fn((arg, parToTp, parFromTp)) bcoerce(parToTp, parFromTp, arg))
  val bapp = bcoerce(fromResTp, toResTp, App(ex, bargs))
  Lam(pars, toEffTp, bapp)

fun zip3(l1: list<a>, l2: list<b>, l3: list<c>): list<(a,b,c)>
  match (l1, l2, l3)
    (Cons(x1, xs1), Cons(x2, xs2), Cons(x3, xs3)) -> Cons((x1, x2, x3), zip3(xs1.unsafe-decreasing, xs2, xs3))
    _ -> Nil

fun boxBindExprAsValue(fromTp: ktype, toTp: ktype, ex: expr, f: expr -> boxEff expr)
  if ex.isTotal then f(ex)
  else
    val v = uniqueTName("bv", fromTp)
    val body = f(Var(v, InfoNone))
    Let([DefNonRec(makeTDef(v, ex))], body)

// type without quantification
fun boxTypeOf(ex: expr)
  match ex.typeOf.splitPredType
    (_, _, tp) -> tp

fun boxType(tp: ktype)
  match tp
    TForAll(_, _, t) -> t.boxType
    TFun(pars, eff, res) -> TFun(pars.map(fn((n, t)) (n, t.boxType)), eff.boxType, res.boxType)
    TApp(t, ts) -> TApp(t.boxType, ts.map(fn(t') t'.kind.typeBox))
    TSyn(syn, args, t) -> TSyn(syn, args.map(boxType), t.boxType)
    _ -> tp

fun boxedFunType(tp: ktype)
  match tp
    TForAll(_, _, t) -> t.boxedFunType
    TSyn(_, _, t) -> t.boxedFunType
    TFun(pars, eff, res) ->
      val bpars = pars.map(fn(_) boxedTypeVar())
      val bres = res.boxedFunType
      TFun(pars.zip(bpars).map(fn(((nm, _), bp)) (nm, bp)), eff, bres)
    _ -> fail("backend/c/box boxedFunType: " ++ tp.pretty.show)

fun boxedTypeVar()
  TVar(TypeVar(newUnique(), kindStar, Bound))

fun typeBox(k: kind)
  TCon(TypeCon(nameTpBox, k))

type cType
  CBox
  CFun(args: list<cType>, res: cType)
  CData

fun cType(k: ktype)
  match k
    TForAll(_, _, t) -> cType(t)
    TFun(pars, res) -> CFun(pars.map(fn((_, t)) cType(t)), cType(res))
    TApp(t) -> t.cType
    TCon -> CData
    TVar -> CBox
    TSyn(_, _, t) -> cType(t)

fun (==)(c1s: list<cType>, c2s: list<cType>): div bool
  match (c1s, c2s)
    (Nil, Nil) -> True
    (Cons(c1, c1s'), Cons(c2, c2s')) -> c1 == c2 && c1s' == c2s'
    _ -> False

fun (==)(c1: cType, c2: cType): div bool
  match (c1, c2)
    (CBox, CBox) -> True
    (CData, CData) -> True
    (CFun(args1, res1), CFun(args2, res2)) -> args1 == args2 && res1 == res2
    _ -> False

fun (!=)(c1: cType, c2: cType): div bool
  !(c1 == c2)

val typeBoxStar = kindStar.typeBox

fun isBoxPat(p: pattern)
  match p
    PatCon(name) -> name.getName == nameBoxCon
    _ -> False

fun patBox(tpPat: ktype, tpRes: ktype, p: pattern)
  PatCon(TName(nameBoxCon, boxConInfo.typeScheme), [p], boxConRepr, [tpPat], [], tpRes, boxConInfo, True)

val boxConRepr = ConSingle(nameTpBox, DataSingle(False), valueReprScan(1), CtxNone, 0)
val tva = TypeVar(0, kindStar, Bound)
val tp = TForAll([tva], [], TFun([(nameNil, TVar(tva))], typeTotal, typeBoxStar))
val boxConInfo = ConInfo(nameBox, nameTpBox, [tva], [], [(nameNil, TVar(tva))], tp, Inductive, rangeNull, [], [Public], True, [(nameNil, TVar(tva))], valueReprScan(1), Public, "") // size is wrong with knowing the platform?

fun uniqueTName(nm: string, tp: ktype)
  val n = uniqueName(nm)
  TName(n, tp)
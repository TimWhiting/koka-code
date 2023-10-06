import compiler/lib/pprint
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/failure
import compiler/common/syntax
import compiler/kind/newtypes
import compiler/kind/kind
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/core/core
import compiler/platform/config

// take a context and check if it is well-formed and return a well-typed context expression
fun analyzeCCtx(rng: range, expr: expr): <compFlags, uniquePhase, pure, newtypes> (expr, list<doc>)
  with handler
    return(x) (x, [])
    final ctl emitCCtxError(e) (expr.typeOf.makeCCtxEmpty, [e])
    final ctl emitCCtxErrors(e) (expr.typeOf.makeCCtxEmpty, e)
  expr.cctxCreate

effect cctxEffect
  final ctl emitCCtxError(d: doc): a
  final ctl emitCCtxErrors(d: list<doc>): a

fun tryC(f: () -> <cctxEffect|e> a): <cctxEffect|e> either<list<doc>,a>
  with override 
    return(x) Right(x)
    final ctl emitCCtxError(e) Left([e])
    final ctl emitCCtxErrors(e) Left(e)
  f()

value struct chole
  addr: expr
  ktype: ktype;

value struct cctx
  defs: list<def>
  top: expr
  hold: chole;

fun cctxCreate(e: expr)
  // empty context
  if e.isHole then e.typeOf.makeCCtxEmpty
  else
    // non-empty context
    val (Cctx(defs, top, Chole(addr, holeTp))) = e.cctxExpr
    val cctx = makeCCtxCreate(top.typeOf, holeTp, top, addr)
    Let(defs.map(DefNonRec), cctx)

fun cctxExpr(e: expr)
  match e
    // constructor 
    App(Con(name, repr), args) | repr.hasCtxPath && args.is-cons ->
      cctxCon(name, repr, [], args)
    App(TypeApp(Con(name, repr), targs), args) | repr.hasCtxPath && args.is-cons ->
      cctxCon(name, repr, targs, args)
    _ -> emitCCtxErrors([])

fun cctxCon(cName: tName, cRepr: conRepr, targs: list<ktype>, args: list<expr>)
  match args.span(fn(a) !a.isHole)
    (pre, Cons(h, post)) ->
      cctxConFinal(cName, cRepr, targs, pre, h, post)
    _ -> cctxConRecurse(cName, cRepr, targs, args)

fun cctxConRecurse(cName: tName, cRepr: conRepr, targs: list<ktype>, args: list<expr>)
  val (pre,cctx,post) = cctxFind([], [], args)
  (pre ++ post).foreach(cctxCheckNoHole)
  val (ds, vars) = pre.map(makeUniqueDef).unzip
  val fname = cName.getFieldName(pre.length + 1)
  val ctxrepr = cRepr.updateCtxPath(CtxField(fname))
  val (d1, var1) = makeUniqueDef(App(makeTypeApp(Con(cName, ctxrepr), targs), vars ++ [cctx.top] ++ post))
  cctx(defs=ds ++ cctx.defs ++ [d1], top=var1)

fun cctxConFinal(cName: tName, cRepr: conRepr, targs: list<ktype>, pre: list<expr>, chole: expr, post: list<expr>)
  (pre ++ post).foreach(cctxCheckNoHole)
  val fname = cName.getFieldName(pre.length + 1)
  val holetp = chole.typeOf
  val ctxrepr = cRepr.updateCtxPath(CtxField(fname))
  holetp.ensureValidHoleType
  val (d1, var1) = makeUniqueDef(App(makeTypeApp(Con(cName, ctxrepr), targs), pre ++ [chole] ++ post))
  val (d2, addr) = makeUniqueDef(makeFieldAddrOf(var1, cName, fname.getName, holetp))
  Cctx([d1, d2], var1, Chole(addr, holetp))

fun cctxCheckNoHole(e: expr): ()
  () // note: not needed as it is already checked during type inference

fun cctxFind(errs: list<doc>, acc: list<expr>, args: list<expr>)
  match args
    // no args
    Nil -> emitCCtxErrors(errs)
    // try recursively
    Cons(arg, args') ->
      match tryC({arg.cctxExpr})
        Left(errs') -> cctxFind(errs ++ errs', Cons(arg, acc), args')
        Right(cctx) -> (acc.reverse, cctx, args')

fun makeUniqueDef(e: expr)
  val name = uniqueName("cctx")
  (makeDef(name, e), Var(TName(name, e.typeOf), InfoNone))

fun isHole(e: expr)
  match e
    App(TypeApp(Var(TName(hname, _htp)), [_tp, _etp]), []) -> hname == nameCCtxHoleCreate
    App(App(TypeApp(Var(open), [_effFrom, _effTo, _tpFrom, _tpTo]), [TypeApp(Var(hname))]), []) ->
      open.getName == nameEffectOpen && hname.getName == nameCCtxHoleCreate
    _ -> False

// Initial empty context (ctx hole)
fun makeCCtxEmpty(tp: ktype)
  val a = TypeVar(0, kindStar, Bound)
  val funType = TForAll([a], [], TFun([], typeTotal, typeCCtx(TVar(a))))
  App(TypeApp(Var(TName(nameCCtxEmpty, funType), InfoExternal([(C(CDefault), "kk_cctx_empty(kk_context())"), (JS(JsDefault), "$std_core_types._cctx_empty()")])), [tp]), [])

// Create a context (ctx Cons(e, Cons(2, hole)))
fun makeCCtxCreate(tp: ktype, holetp: ktype, top: expr, holeaddr: expr)
  val a = TypeVar(0, kindStar, Bound)
  val b = TypeVar(1, kindStar, Bound)
  val funType = TForAll([a, b], [], 
    TFun([(nameNil, TVar(a)), (nameNil, TApp(typeFieldAddr, [TVar(a)]))], 
      typeTotal, TApp(typeCCtxx, [TVar(a), TVar(b)])))
  App(TypeApp(Var(TName(nameCCtxCreate, funType), 
    InfoExternal([(C(CDefault), "kk_cctx_create(#1,#2,kk_context())"), (JS(JsDefault), "$std_core_types._cctx_create(#1,#2)")])), 
    [tp, holetp]), [top, holeaddr])

// The address of a field in a constructor (for context holes)
fun makeFieldAddrOf(obj: expr, cName: tName, fieldName: name, fieldTp: ktype)
  val a = TypeVar(0, kindStar, Bound)
  val funType = TForAll([a], [], TFun([(nameNil, TVar(a)), (nameNil, typeString), (nameNil, typeString)], typeTotal, TApp(typeFieldAddr, [TVar(a)])))
  App(TypeApp(Var(TName(nameFieldAddrOf, funType), InfoExternal([])), [fieldTp]), [obj, ELit(LitString(showTupled(cName.getName))), ELit(LitString(showTupled(fieldName)))])

// Set the index of the field in a constructor to follow the path to the hole at runtime.
fun makeCCtxSetContextPath(obj: expr, cName: tName, fieldName: name)
  val tp = obj.typeOf
  val funType = TFun([(nameNil, tp), (nameNil, typeString), (nameNil, typeString)], typeTotal, tp)
  App(Var(TName(nameCCtxSetCtxPath, funType), InfoExternal([(DefaultTarget, ".cctx-setcp(#1,#2,#3)")])), 
    [obj, ELit(LitString(showTupled(cName.getName))), ELit(LitString(showTupled(fieldName)))])


fun getFieldName(cName: tName, fieldIdx: int)
  match cName.lookupFieldName(fieldIdx)
    Left(err) -> fail("core/analysiscctx: " ++ err)
    Right(name) -> name

fun ensureValidHoleType(tp: ktype)
  match tp.dataTypeNameOf 
    Left(TVar) -> emitCCtxError("the hole in the constructor context has an unresolved or polymorphic type".text)
    Left -> emitCCtxError("the hole in the constructor context has an invalid data type".text)
    Right(nm) -> 
      match newtypesLookupAny(nm)
        Just(dataInfo) ->
          val (drepr, _) = dataInfo.dataRepr(isValue)
          if dataInfo.def.isValue || drepr.isValue then
            emitCCtxError("the hole in a constructor context cannot be a value type".text)
          ()

fun dataTypeNameOf(tp: ktype)
  match tp.expandSyn
    TApp(t) -> t.dataTypeNameOf
    TCon(tc) -> Right(tc.name)
    t -> Left(t)

fun getDataTypeNameRes(tp: ktype)
  match tp.dataTypeNameOf
    Right(name) -> name
    Left(t) -> fail("core/ctail getDataTypeNameRes: illegal result type: " ++ t.show)

fun getDataTypeName(cName: tName)
  match cName.tNameType.splitFunScheme
    Just((_, _, _, _, tres)) -> tres.getDataTypeNameRes
    _ -> fail("core/ctail getFieldName: illegal constructor type: " ++ cName.show)

fun lookupFieldName(cName: tName, fieldIdx: int)
  match newtypesLookupAny(cName.getDataTypeName)
    Just(dinfo) ->
      val (drepr, _) = dinfo.dataRepr(isValue)
      if drepr.isValue then
        Left("contexts cannot go through a value type (" ++ cName.getName.show ++ ")")
      else
        match dinfo.constrs.filter(fn(c) c.name == cName.getName)
          [c] -> 
            match c.params.drop(fieldIdx - 1)
              Cons((fname, ftp)) -> Right(TName(fname, ftp))
              _ -> fail("core/ctail getFieldName: field index is off: " ++ cName.show ++ ", field " ++ fieldIdx.show ++ ", in " ++ c.params.show-list(fn((n, _)) n.show))
          _ -> fail("core/ctail getFieldName: constructor not found: " ++ cName.show ++ ", field " ++ fieldIdx.show ++ ", in " ++ dinfo.constrs.map(show).join(","))
      
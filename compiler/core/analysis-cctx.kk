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
fun analyze(rng: range, expr: expr): <comp-flags, uniquePhase, pure, newtypesEff> (expr, list<doc>)
  with handler
    return(x) (x, [])
    final ctl emit-ctx-err(e) (expr.type-of.make-empty, [e])
    final ctl emit-ctx-errs(e) (expr.type-of.make-empty, e)
  expr.cctx-create

effect cctx-eff
  final ctl emit-ctx-err(d: doc): a
  final ctl emit-ctx-errs(d: list<doc>): a

fun tryC(f: () -> <cctx-eff|e> a): <cctx-eff|e> either<list<doc>,a>
  with override 
    return(x) Right(x)
    final ctl emit-ctx-err(e) Left([e])
    final ctl emit-ctx-errs(e) Left(e)
  f()

value struct chole
  addr: expr
  ktype: ktype;

value struct cctx
  defs: list<def>
  top: expr
  hold: chole;

fun cctx-create(e: expr)
  // empty context
  if e.is-hole then e.type-of.make-empty
  else
    // non-empty context
    val (Cctx(defs, top, Chole(addr, holeTp))) = e.expr
    val cctx = make-create(top.type-of, holeTp, top, addr)
    Let(defs.map(DefNonRec), cctx)

fun expr(e: expr)
  match e
    // constructor 
    App(Con(name, repr), args) | repr.hasCtxPath && args.is-cons ->
      make-con(name, repr, [], args)
    App(TypeApp(Con(name, repr), targs), args) | repr.hasCtxPath && args.is-cons ->
      make-con(name, repr, targs, args)
    _ -> emit-ctx-errs([])

fun make-con(cName: tName, cRepr: conRepr, targs: list<ktype>, args: list<expr>)
  match args.span(fn(a) !a.is-hole)
    (pre, Cons(h, post)) ->
      con-final(cName, cRepr, targs, pre, h, post)
    _ -> con-recurse(cName, cRepr, targs, args)

fun con-recurse(cName: tName, cRepr: conRepr, targs: list<ktype>, args: list<expr>)
  val (pre,cctx,post) = find([], [], args)
  (pre ++ post).foreach(check-no-hole)
  val (ds, vars) = pre.map(make-unique-def).unzip
  val fname = cName.get-field-name(pre.length + 1)
  val ctxrepr = cRepr.updateCtxPath(CtxField(fname))
  val (d1, var1) = make-unique-def(App(makeTypeApp(Con(cName, ctxrepr), targs), vars ++ [cctx.top] ++ post))
  cctx(defs=ds ++ cctx.defs ++ [d1], top=var1)

fun con-final(cName: tName, cRepr: conRepr, targs: list<ktype>, pre: list<expr>, chole: expr, post: list<expr>)
  (pre ++ post).foreach(check-no-hole)
  val fname = cName.get-field-name(pre.length + 1)
  val holetp = chole.type-of
  val ctxrepr = cRepr.updateCtxPath(CtxField(fname))
  holetp.ensure-valid-hole-type
  val (d1, var1) = make-unique-def(App(makeTypeApp(Con(cName, ctxrepr), targs), pre ++ [chole] ++ post))
  val (d2, addr) = make-unique-def(make-field-addr-of(var1, cName, fname.get-name, holetp))
  Cctx([d1, d2], var1, Chole(addr, holetp))

fun check-no-hole(e: expr): ()
  () // note: not needed as it is already checked during type inference

fun find(errs: list<doc>, acc: list<expr>, args: list<expr>)
  match args
    // no args
    Nil -> emit-ctx-errs(errs)
    // try recursively
    Cons(arg, args') ->
      match tryC({arg.expr})
        Left(errs') -> find(errs ++ errs', Cons(arg, acc), args')
        Right(cctx) -> (acc.reverse, cctx, args')

fun make-unique-def(e: expr)
  val name = unique-name("cctx")
  (makeDef(name, e), Var(TName(name, e.type-of), InfoNone))

fun is-hole(e: expr)
  match e
    App(TypeApp(Var(TName(hname, _htp)), [_tp, _etp]), []) -> hname == nameCCtxHoleCreate
    App(App(TypeApp(Var(open), [_effFrom, _effTo, _tpFrom, _tpTo]), [TypeApp(Var(hname))]), []) ->
      open.get-name == nameEffectOpen && hname.get-name == nameCCtxHoleCreate
    _ -> False

// Initial empty context (ctx hole)
fun make-empty(tp: ktype)
  val a = TypeVar(0, kindStar, Bound)
  val funType = TForAll([a], [], TFun([], typeTotal, typeCCtx(TVar(a))))
  App(TypeApp(Var(TName(nameCCtxEmpty, funType), InfoExternal([(C(CDefault), "kk_cctx_empty(kk_context())"), (JS(JsDefault), "$std_core_types._cctx_empty()")])), [tp]), [])

// Create a context (ctx Cons(e, Cons(2, hole)))
fun make-create(tp: ktype, holetp: ktype, top: expr, holeaddr: expr)
  val a = TypeVar(0, kindStar, Bound)
  val b = TypeVar(1, kindStar, Bound)
  val funType = TForAll([a, b], [], 
    TFun([(nil, TVar(a)), (nil, TApp(typeFieldAddr, [TVar(a)]))], 
      typeTotal, TApp(typeCCtxx, [TVar(a), TVar(b)])))
  App(TypeApp(Var(TName(nameCCtxCreate, funType), 
    InfoExternal([(C(CDefault), "kk_cctx_create(#1,#2,kk_context())"), (JS(JsDefault), "$std_core_types._cctx_create(#1,#2)")])), 
    [tp, holetp]), [top, holeaddr])

// The address of a field in a constructor (for context holes)
fun make-field-addr-of(obj: expr, cName: tName, fieldName: name, fieldTp: ktype)
  val a = TypeVar(0, kindStar, Bound)
  val funType = TForAll([a], [], TFun([(nil, TVar(a)), (nil, typeString), (nil, typeString)], typeTotal, TApp(typeFieldAddr, [TVar(a)])))
  App(TypeApp(Var(TName(nameFieldAddrOf, funType), InfoExternal([])), [fieldTp]), [obj, ELit(LitString(show-tupled(cName.get-name))), ELit(LitString(show-tupled(fieldName)))])

// Set the index of the field in a constructor to follow the path to the hole at runtime.
fun make-set-ctx-path(obj: expr, cName: tName, fieldName: name)
  val tp = obj.type-of
  val funType = TFun([(nil, tp), (nil, typeString), (nil, typeString)], typeTotal, tp)
  App(Var(TName(nameCCtxSetCtxPath, funType), InfoExternal([(DefaultTarget, ".cctx-setcp(#1,#2,#3)")])), 
    [obj, ELit(LitString(show-tupled(cName.get-name))), ELit(LitString(show-tupled(fieldName)))])


fun get-field-name(cName: tName, fieldIdx: int)
  match cName.lookup(fieldIdx)
    Left(err) -> fail("core/analysiscctx: " ++ err)
    Right(name) -> name

fun ensure-valid-hole-type(tp: ktype)
  match tp.data-type-name-of 
    Left(TVar) -> emit-ctx-err("the hole in the constructor context has an unresolved or polymorphic type".text)
    Left -> emit-ctx-err("the hole in the constructor context has an invalid data type".text)
    Right(nm) -> 
      match newtypesLookupAny(nm)
        Just(dataInfo) ->
          val (drepr, _) = dataInfo.dataRepr(is-value)
          if dataInfo.def.is-value || drepr.is-value then
            emit-ctx-err("the hole in a constructor context cannot be a value type".text)
          ()

fun data-type-name-of(tp: ktype)
  match tp.expandSyn
    TApp(t) -> t.data-type-name-of
    TCon(tc) -> Right(tc.name)
    t -> Left(t)

fun data-type-name-res(tp: ktype)
  match tp.data-type-name-of
    Right(name) -> name
    Left(t) -> fail("core/ctail data-type-name-res: illegal result type: " ++ t.show)

fun data-type-name(cName: tName)
  match cName.type-of.splitFunScheme
    Just((_, _, _, _, tres)) -> tres.data-type-name-res
    _ -> fail("core/ctail get-data-type-name: illegal constructor type: " ++ cName.show)

fun lookup(cName: tName, fieldIdx: int)
  match newtypesLookupAny(cName.data-type-name)
    Just(dinfo) ->
      val (drepr, _) = dinfo.dataRepr(is-value)
      if drepr.is-value then
        Left("contexts cannot go through a value type (" ++ cName.get-name.show ++ ")")
      else
        match dinfo.constrs.filter(fn(c) c.name == cName.get-name)
          [c] -> 
            match c.params.drop(fieldIdx - 1)
              Cons((fname, ftp)) -> Right(TName(fname, ftp))
              _ -> fail("core/ctail get-field-name: field index is off: " ++ cName.show ++ ", field " ++ fieldIdx.show ++ ", in " ++ c.params.show-list(fn((n, _)) n.show))
          _ -> fail("core/ctail get-field-name: constructor not found: " ++ cName.show ++ ", field " ++ fieldIdx.show ++ ", in " ++ dinfo.constrs.map(show).join(","))
      
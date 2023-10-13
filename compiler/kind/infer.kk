// Responsibilities of the kind checker:
// - Kindcheck all types in the program
// - Translate user types to internal types
// - Collect lists of data types, synonyms and constructors
// - Expand all synonyms (i.e., replace @id(int)@ by @id(int) == int@)
// - Transate type definition groups and externals to Core.
import compiler/lib/pprint
import compiler/common/failure
import compiler/common/color-scheme
import compiler/common/range
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/file
import compiler/syntax/syntax
import compiler/syntax/range-map
import compiler/core/core
import compiler/kind/importmap
import compiler/kind/kind
import compiler/kind/assumption
import compiler/kind/constructors
import compiler/kind/newtypes
import compiler/kind/synonyms
import compiler/kind/repr
import compiler/type/type
import compiler/type/assumption
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/kind
import compiler/kind/infer-kind
import compiler/kind/infer-effect
import compiler/kind/unify
import newstd/data/linearset
import newstd/data/linearmap

// Kindcheck a program and calculate types
fun inferKinds(
      isValue: (dataInfo) -> pure bool, // is this a value type
      target: platform, // target platform (x32, x64)
      mbRangeMap: maybe<range-map>, // range map for tool integration
      imports: importmap, // import aliases
      kgamma0: kGamma, // initial kind kgamma
      syns0: synonyms, // initial list of synonyms
      data0: newtypes, // initial list of data types
      Program(source, modName, nmrng, tdgroups, defs, importdefs, externals, fixdefs, doc): program<userType, userKind>) // original program
  val (errs1, warns1, rm1, (cgroups, kgamma1, syns1, data1)) = runKindInfer(platform, mbRangeMap, modName, imports, kgamma0, syns0, data0, fn() infTypeDefGroups(tdgroups))
  val (errs2, warns2, rm2, externals1) = runKindInfer(platform, mbRangeMap, modName, imports, kgamma1, syns1, data1, fn() infExternals(externals))
  val (errs3, warns3, rm3, defs1) = runKindInfer(platform, mbRangeMap, modName, imports, kgamma2, syns2, data2, fn() infDefGroups(defs))
  val (synInfos, dataInfos) = cgroups.extractInfos.unzipEither
  val conInfos = dataInfos.map(dataInfoConstrs).concat
  val cons1 = conInfos.constructorsFromList
  val gamma1 = dataInfos.constructorGamma(isValue)
  val errg4 = conInfos.constructorCheckDuplicates
  val errs = errs1 ++ errs2 ++ errs3 ++ errs4
  val warns = warns1 ++ warns2 ++ warns3
  val dgroups = cgroups.map(fn(cgroup) cgroup.synTypeDefGroup(modName))
  addWarnings(warns)
  if errs.is-nil then 
    (dgroups ++ defs1, kgamma1, syns1, data1, cons1, Core(modName, [], [], cgroups, [], externals1, doc), rm3)
  else
    errMsg(ErrorKind(errs))
  
fun unzipEither(xs: list<either<a, b>>): (list<a>, list<b>)
  fun loop(ys: list<either<a, b>>, las: ctx<list<a>>, lbs: ctx<list<b>>): (list<a>, list<b>)
    match ys
      Nil -> (las ++. Nil, lbs ++. Nil)
      Cons(Left(a), a1) -> loop(a1, las ++ ctx Cons(a, _), lbs)
      Cons(Right(b), b1) -> loop(b1, las, lbs ++ ctx Cons(b, _))
  loop(xs, ctx _, ctx _)

fun extractInfos(groups: list<compiler/core/core/typeDefGroup>): list<either<synInfo, dataInfo>>
  fun extractInfo(td: compiler/core/core/typeDef): either<synInfo, dataInfo>
    match td
      compiler/core/core/Synonym(si) -> Left(si)
      Data(di) -> Right(di)
  fun extractGroupInfos(g: compiler/core/core/typeDefGroup): list<either<synInfo, dataInfo>>
    g.map(extractInfo)
  groups.map(extractGroupInfos).concat

fun synTypeDefGroup(tdg: compiler/core/core/typeDefGroup, modName: name): compiler/syntax/syntax/defGroups<ktype>
  tdg.map(fn(td) td.synTypeDef(modName)).concat

fun synTypeDef(td: compiler/core/core/typeDef, modName: name): list<compiler/syntax/syntax/defGroup<ktype>>
  match td
    compiler/core/core/Synonym -> []
    Data(di) | di.name.isHiddenName -> []
    Data(di, isExtend) ->
      di.synAccessors(modName) ++ (
        if di.constrs.length == 1 && !di.isOpen && !di.constrs.head.unjust.name.isHiddenName && di.kind.hasKindStarResult then
          [synCopyCon(di, modName, di.constrs.head)]
        else []
      ) ++ (
        if di.constrs.length > 1 && di.isOpen then
          di.constrs.map(fn(ci) ci.synTester(di)).concat
        else []
      ) ++ (
        if di.isOpen then di.constrs.map(synConstrTag) else []
      )

fun synCopyCon(di: dataInfo, ci: conInfo, modName: name)
  val rc = ci.range
  val tp = TypeApp(TCon(TypeCon(di.name, di.kind)), di.params(fn(TypeVar(id, kind)) TVar(id, kind, Meta)))
  val argName = ".this".newName
  val fullTp = 
    val (vars, preds, rho) = ci.t.splitPredType
    match rho.splitFunType
      Just((args, eff, res)) -> TForAll(vars, preds, TFun([(argName, res)] ++ args.map(fn((nm, t)) (nm, if !ci.hasAccessor(nm, t) then t else t.makeOptional)), eff, res))
      Nothing -> TForAll(vars, preds, TFun([(argName, rho)], typeTotal, rho))
  fun vvar(n)
    Var(n, False, rc)
  fun app(x, xs)
    if xs.is-nil then x else App(x, xs.map(fn(y) (Nothing, y)), rc)
  val params = ci.params.map(fn((nm, t)) ValueBinder(nm, Nothing, if !ci.hasAccessor(nm, t) then Nothing else Just(app(vvar(nm), [vvar(argName)]))), rc, rc)
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rc, rc)] ++ params, body, rc)
  val body = app(vvar(ci.name), ci.params.map(fn((nm, _)) vvar(nm)))
  DefNonRec(Def(ValueBinder(nameCopy, (), Ann(expr, fullTp, rc), rc, rc), rc, di.vis, defFun([]), InlineAuto, ""))

fun hasAccessor(ci: conInfo, nm: name, tp: ktype)
  val tvs = tp.freeTypeVars
  !(nm.isFieldName || nm == nameNil) && ci.existentials.all(fn(tv) !tvs.member(tv))

fun nubBy(xs: list<a>, f: (a, a) -> bool): list<a>
  match xs
    Cons(x1, rst) -> Cons(x1, rst.filter(fn(y) !f(x1, y)))
    Nil -> Nil

fun is-alphanum(c: char)
  c.is-alpha || c.is-digit

fun synAccessors(di: dataInfo, modName: name)
  val paramss = di.constrs.map(fn(ci) ci.params.zipwith(ci.paramVis.zip(ci.paramRanges)) fn((nm, tp), (pvis, rng))
    (nm, (tp, rng, pvis, ci))
  )
  fun occursOnAllConstrs((nm, (tp, _, _, _)))
    paramss.all(fn(ps) ps.any(fn((n, (t, _, _, _))) n == nm && t == tp))
  val fields = paramss.concat.filter(fn((nm, (tp, _, _, cinfo))) cinfo.hasAccessor(nm, tp)).nubBy(fn(x, y) x.fst == y.fst).filter(occursOnAllConstrs)
  fun synAccessor((nm, (tp, rng, vis, cinfo)))
    val dataName = di.name.unqualify
    val arg = if dataName.show.list.all(is-alphanum) then dataName else ".this".newName
    val fld = ".x".newName
    val dataTp = TypeApp(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
    val fullTp = 
      val (vars, preds, rho) = tp.splitPredType
      TForAll(di.params ++ foralls, preds, TypeFun([(arg, dataTp)], if isPartial then typePartial else typeTotal, rho))
    fun makeBranch(ci: conInfo)
      val r = ci.range
      match zip(ci.params, list(0, ci.params.length)).lookup(fn(n) n == nm)
        Just(i) ->
          val patterns = list(0, i - 1).map(fn(_) (Nothing, PatWild(r))) ++ [(Nothing, PatVar(ValueBinder(fld, Nothing, PatWild(r), r, r)))] ++ list(i+1, ci.params.length - 1).map(fn(_) (Nothing, PatWild(r)))
          [(ci.vis, Branch(PatCon(ci.name, patterns, r, r), [Guard(guardTrue, Var(fld, False, r))]))]
        _ -> []
    val messages = [Literal(LitString(rng.start.source.name ++ rng.show, rng)), Literal(LitString(nm.show, rng))]
    val doc = "// Automatically generated. Retrieves the `" ++ nm.show ++ "` constructor field of the `" ++ di.name.nameId ++ "` type.\n"
    val defaultBranch = if isPartial then [Branch(PatWild(rng), [Guard(guardTrue, App(Var(namePatternMatchError, False, rng), message.map(fn(msg) (Nothing, msg)), rng))])]
    val branches = di.constrs.map(makeBranch).concat
    val isPartial = branches.length < di.constrs.length || di.isOpen
    val caseExpr = Case(Var(arg, False, rng), branches.map(snd) ++ defaultBranch, rng)
    val expr = Ann(Lam([ValueBinder(arg, Nothing, Nothing, rng, rng)], caseExpr, rng), fullTp, rng)
    DefNonRec(Def(ValueBinder(nm, (), expr, rng, rng), rng, vis, defFunEx([Borrow], noFip), InlineAlways, doc))
  fields.map(synAccessor)

fun synTester(di: dataInfo, ci: conInfo)
  if ci.name.isHiddenName then []
  else
    val defName = "is-".prepend(ci.name.unqualify.toVarName)
    val arg = di.name.unqualify
    val rc = ci.range
    val patterns = ci.params.map(fn(_) (Nothing, PatWild(rc)))
    val branch1 = Branch(PatCon(ci.name, patterns, rc, rc), [Guard(guardTrue, Var(nameTrue, False, rc))])
    val branch2 = Branch(PatWild(rc), [Guard(guardTrue, Var(nameFalse, False, rc))])
    val caseExpr = Case(Var(arg, False, rc), [branch1, branch2], rc)
    val expr = Lam([ValueBinder(arg, Nothing, Nothing, rc, rc)], caseExpr, rc)
    val doc = "// Automatically generated. Tests for the `" ++ ci.name.nameId ++ "` constructor of the `:" ++ di.name.nameId ++ "` type.\n"
    [DefNonRec(Def(ValueBinder(defName, (), expr, rc, rc), rc, ci.vis, defFunEx([Borrow], Fip(AllocAtMost(0))), InlineAlways, doc))]

fun synConstrTag(ci: conInfo)
  val nm = ci.name.unqualify.toOpenTagName
  val rc = ci.range
  val expr = Literal(LitString(ci.name.show, rc))
  DefNonRec(Def(ValueBinder(nm, (), expr, rc, rc), rc, ci.vis, DefVal, InlineNever, ""))

// Infer kinds for type definition groups
fun infTypeDefGroups(tdgs: list<compiler/syntax/syntax/typeDefGroup<userType,userKind>>)
  match tdgs
    Nil -> (Nil, infKindEnv.kGamma, infKindEnv.synonyms, infKindEnv.allnewtypes)
    Cons(tdgroup, tdgroups) ->
      val ctdgroup = infTypeDefGroup(tdgroup)
      with extendKGamma(tdgroup.getRanges, ctdgroup)
      val (ctdgroups, kgamma1, syns1, data1) = infTypeDefGroups(tdgroups)
      Cons(ctdgroup, kgamma1, syns1, data1)

fun infTypeDefGroup(td: compiler/syntax/syntax/typeDefGroup<userType,userKind>)
  match td
    TypeDefRec(tdefs) -> infTypeDefs(True, tdefs)
    TypeDefNonRec(tdef) -> infTypeDefs(False, [tdef])

fun infTypeDefs(isRec: bool, tdefs: list<compiler/syntax/syntax/typeDef<userType, userType, userKind>>)
  val xinfgamma = tdefs.map(bindTypeDef) // set up recursion
  val infgamma = xinfgamma.filter(snd).map(fst)
  with extendInfGamma(infgamma)
  val names = infgamma.map(tbinderName)
  val tdefs1 = xinfgamma.map(fst).zip(tdefs).map(infTypeDef)
  val ctdefs = tdefs1.map(fn(d) d.resolveTypeDef(isRec, names))
  checkRecursion(tdefs) // check for recursive type synonym definitions rather late so we spot duplicate definitions first
  compiler/core/core/TypeDefGroup(ctdefs)

fun checkRecursion(tdefs: list<compiler/syntax/syntax/typeDef<userType, userType, userKind>>)
  if tdefs.length <= 1 || tdefs.any(is-dataType) then
    ()
  else
    addError("Type synonyms cannot be recursive".text, if tdefs.length > 0 then tdefs.head.unjust.range.combine(tdefs.last.unjust.range) else rangeNull)

// Setup type environment for recursive definitions
fun bindTypeDef(tdef: compiler/syntax/syntax/typeDef<userType, userType, userKind>)
  val TypeBinder(name, kind, rngName, rng) = bindTypeBinder(tdef.binder)
  val isExtend = 
    match tdef
      DataType(isExtend=yes) -> yes
      _ -> False
  val qname = if isExtend then name else name.qualifyDef
  (TypeBinder(qname, kind, rngName, rng), !isExtend)

fun bindTypeBinder(TypeBinder(name, userKind, rngName, rng): typeBinder<userKind>)
  val kind = userKindToKind(userKind)
  TypeBinder(name, kind, rngName, rng)

fun userKindToKind(userKind: userKind)
  match userKind
    KindCon(nm) -> KICon(KCon(nm))
    KindArrow(k1, k2) ->
      val k1' = userKindToKind(k1)
      val k2' = userKindToKind(k2)
      match (k1', k2')
        (KICon(kk1), KICon(kk2)) -> KICon(kindFun(kk1, kk2))
        _ -> KIApp(k1', k2')
    KindParens(k) -> userKindToKind(k)
    KindNone -> freshKind()

// Infer kinds of external definitions
fun infExternals(externals0: list<compiler/syntax/syntax/external>)
  fun walk(names: list<name>, externals: list<compiler/syntax/syntax/external>)
    match externals
      Nil -> Nil
      Cons(ex, exs) ->
        val (ext, names2) = ex.infExternal(names)
        val exts = walk(names2, exs)
        Cons(ext, exts)
  walk([], externals0)

fun infExternal(ex: compiler/syntax/syntax/external, names: list<name>)
  match ex
    compiler/syntax/syntax/External(name, tp, pinfos, nameRng, rng, calls, vis, fipT, doc) ->
      with override val uctx = Check("Externals must be values", rng)
      val tp' = tp.infResolveType()
      val qname = name.qualifyDef
      val cname = canonicalName(names.filter(fn(n) n == qname).length, qname)
      if name.isHiddenName then ()
      else
        addRangeInfo(nameRng, RIId(qname, NIValue(tp'), True))
        addRangeInfo(rng, RIDecl("external", qname, cname.mangle(tp')))
      (compiler/core/core/External(cname, tp', pinfos, calls.map(fn(c) c.formatCall(tp')), vis, fipT, nameRng, doc), Cons(qname, names))
    compiler/syntax/syntax/ExternalImport(imps, rng) -> (compiler/core/core/ExternalImport(imps, rng), names)

fun formatCall((target, externalCall): (target, externalCall), tp: ktype)
  match externalCall
    ExternalInline(inl) -> (target, inl)
    ExternalCall(fname) ->
      val (foralls, _, rho) = tp.splitPredType
      val argumentCount = match rho.splitFunType
        Just((args, _, _)) -> args.length
        _ -> 0
      val arguments = "(" ++ list(1, argumentCount).map(fn(i) "#" ++ i.show).join(",") ++ ")"
      val argumentsC = "(" ++ list(1, argumentCount).map(fn(i) "#" ++ i.show).join(",") ++ (if fname.starts-with("kk_").is-just then "kk_context()" else "") ++ ")"
      val typeArguments = if foralls.is-nil then "" else "<" ++ list(1, foralls.length).map(fn(v) "##" ++ v.show).join(",") ++ ">"
      match target
        CS -> (target, fname ++ typeArguments ++ arguments)
        JS -> (target, fname ++ arguments)
        C -> (target, fname ++ argumentsC)
        DefaultTarget -> (target, fname ++ arguments)

fun infResolveType(tp: userType)
  val infTp = infUserType(infKindStar, tp)
  resolveType(nameTVMapEmpty, False, infTp)

fun infResolveHX(tp: userType)
  val infTp = infUserType(infKindHandled, tp)
  resolveType(nameTVMapEmpty, False, infTp)

fun infResolveX(tp: userType, rng: range)
  val ikind = freshKind()
  val infTp = infUserType(ikind, tp)
  val skind = subst(ikind)
  // also allow effect label constructors without giving type parameters
  val (kargs, _) = skind.infExtractKindFun
  if kargs.is-cons then
    val vars = kargs.map-indexed(fn(i, _) newName("_" ++ i.show))
    val quals = vars.map(fn(nm) TypeBinder(nm, KindNone, rng, rng))
    val tpvars = vars.map(fn(nm) TpVar(nm, rng))
    val newTp = quals.foldr(TpApp(tp, tpvars, rng), fn(q, t) TpQuan(QSome, q, t, rng))
    newTp.infResolveX(rng) // recurse
  else
    // auto upgrade bare labels of HX or HX1 to X kind labels.
    val eff = match skind
      KICon(k) | k == kindLabel -> infTp
      KICon(k) | k == kindHandled -> makeHandled(infTp, rng)
      KICon(k) | k == kindHandled1 -> makeHandled1(infTp, rng)
      _ -> 
        unify(rng, infKindLabel, skind)
        infTp
    resolveType(nameTVMapEmpty, False, eff)

// Infer kinds of definitions
fun infDefGroups(dgs: list<compiler/syntax/syntax/defGroup<userType>>)
  dgs.map(infDefGroup)

fun infDefGroup(dg: compiler/syntax/syntax/defGroup<userType>)
  match dg
    compiler/syntax/syntax/DefRec(defs) -> DefRec(defs.map(infDef))
    compiler/syntax/syntax/DefNonRec(def) -> DefNonRec(infDef(def))

fun infDef(compiler/syntax/syntax/Def(binder, rng, vis, isVal, inl, doc): compiler/syntax/syntax/def<userType>)
  Def(binder.infValueBinder, rng, vis, isVal, inl, doc)

fun infValueBinder(ValueBinder(nm, u, x, nmRng, rng): valueBinder<(), compiler/syntax/syntax/expr<userType>>)
  ValueBinder(nm, u, x.infExpr, nmRng, rng)

fun infLamValueBinder(ValueBinder(nm, mbTp, x, nmRng, rng): valueBinder<maybe<userType>, maybe<compiler/syntax/syntax/expr<userType>>>)
  val mbTp' = mbTp.map(
    fn(t)
      with override val uctx = Check("Function parameters must be values", rng)
      t.infResolveType()
  )
  ValueBinder(nm, mbTp', x.map(infExpr), nmRng, rng)

fun infPatValueBinder(ValueBinder(nm, mbTp, pat, nmRng, rng): valueBinder<maybe<userType>, compiler/syntax/syntax/pattern<userType>>)
  val mbTp' = mbTp.map(
    fn(t)
      with override val uctx = Check("Matched expressions must be values", rng)
      t.infResolveType()
  )
  ValueBinder(nm, mbTp', pat.infPat, nmRng, rng)

fun infHandlerValueBinder(ValueBinder(nm, mbTp, u, nmRng, rng): valueBinder<maybe<userType>, ()>)
  val mbTp' = mbTp.map(
    fn(t)
      with override val uctx = Check("Handler parameters must be values", rng)
      infResolveType(t)
  )
  ValueBinder(nm, mbTp', u, nmRng, rng)

fun infExpr(ex: compiler/syntax/syntax/expr<userType>)
  match ex
    compiler/syntax/syntax/Lam(binds, expr, rng) -> compiler/syntax/syntax/Lam(binds.map(infLamValueBinder), expr.infExpr, rng)
    compiler/syntax/syntax/Let(defs, expr, rng) -> compiler/syntax/syntax/Let(defs.infDefGroup, expr.infExpr, rng)
    compiler/syntax/syntax/Bind(def, expr, rng) -> compiler/syntax/syntax/Bind(def.infDef, expr.infExpr, rng)
    compiler/syntax/syntax/App(f, nargs, rng) -> compiler/syntax/syntax/App(f.infExpr, nargs.map(fn((nm, arg)) (nm, arg.infExpr)), rng)
    compiler/syntax/syntax/Var(nm, isOp, rng) -> compiler/syntax/syntax/Var(nm.infQualifiedName(rng), isOp, rng)
    Literal(l) -> Literal(l)
    Ann(expr, tp, rng) -> 
      val expr' = expr.infExpr
      val tp' = 
        with override val uctx = Check("Expressions must be values", rng) 
        tp.infResolveType()
      Ann(expr', tp', rng)
    compiler/syntax/syntax/Case(expr, brs, rng) -> compiler/syntax/syntax/Case(expr.infExpr, brs.map(infBranch), rng)
    compiler/syntax/syntax/Parens(expr, nm, rng) -> compiler/syntax/syntax/Parens(expr.infExpr, nm, rng)
    Handler(hsort, scoped, over, allowMask, meff, pars, reinit, ret, fin, ops, hrng, rng) ->
      val pars' = pars.map(infHandlerValueBinder)
      val meff' = meff.map() fn(eff)
        with override val uctx = Check("Handler effects must be effect constants (of kind X)", hrng)
        eff.infResolveX(rng)
      Handler(hsort, scoped, over, allowMask, meff', pars', reinit.map(infExpr), ret.map(infExpr), fin.map(infExpr), ops.map(infHandlerBranch), hrng, rng)
    Inject(tp, expr, b, rng) ->
      val expr' = expr.infExpr
      val tp' =
        with override val uctx = Check("Can only inject effect constants", rng)
        tp.infResolveX(rng)
      Inject(tp', expr', b, rng)

fun infPat(p: compiler/syntax/syntax/pattern<userType>)
  match p
    compiler/syntax/syntax/PatWild(rng) -> compiler/syntax/syntax/PatWild(rng)
    compiler/syntax/syntax/PatLit(l) -> compiler/syntax/syntax/PatLit(l)
    compiler/syntax/syntax/PatVar(binder) -> compiler/syntax/syntax/PatVar(binder.infPatValueBinder)
    compiler/syntax/syntax/PatAnn(pat, tp, rng) ->
      val pat' = pat.infPat
      val tp' = 
        with override val uctx = Check("Patterns must be values", rng)
        tp.infResolveType()
      compiler/syntax/syntax/PatAnn(pat', tp', rng)
    compiler/syntax/syntax/PatCon(name, args, r1, r2) -> compiler/syntax/syntax/PatCon(name, args.map(fn((mbNm, p')) (mbNm, p'.infPat)), r1, r2)
    compiler/syntax/syntax/PatParens(pat, rng) -> compiler/syntax/syntax/PatParens(pat.infPat, rng)

fun infHandlerBranch(HandlerBranch(name, pars, expr, opSort, nmRng, rng): handlerBranch<userType>)
  val pars' = pars.map(infHandlerValueBinder)
  val expr' = expr.infExpr
  HandlerBranch(name, pars', expr', opSort, nmRng, rng)

fun infBranch(compiler/syntax/syntax/Branch(pat, guards): compiler/syntax/syntax/branch<userType>)
  val pat' = pat.infPat
  val guards' = guards.map(infGuard)
  compiler/syntax/syntax/Branch(pat', guards')

fun infGuard(compiler/syntax/syntax/Guard(test, body): compiler/syntax/syntax/guard<userType>)
  val test' = test.infExpr
  val body' = body.infExpr
  compiler/syntax/syntax/Guard(test', body')

// Infer the kinds for a type definition
fun infTypeDef(tb: typeBinder<infKind>, td: compiler/syntax/syntax/typeDef<userType, userType, userKind>)
  match td
    compiler/syntax/syntax/Synonym(_, args, tp, rng, vis, doc) ->
      val infgamma = args.map(bindTypeBinder)
      val k = freshKind()
      with extendInfGamma(infgamma)
      with override val uctx = Infer(rng)
      val tp' = infUserType(k, tp)
      val tbinder = unifyBinder(tb, rng, infgamma, k)
      compiler/syntax/syntax/Synonym(tbinder, infgamma, tp', rng, vis, doc)
    DataType(newTp, args, constrs, rng, vis, sort, ddef, isExtend, doc) ->
      val infgamma = args.map(bindTypeBinder)
      with extendInfGamma(infgamma)
      val constrs' = constrs.map(infConstr)
      // TODO: unify extended datatype kind with original
      val resKind = if ddef.isOpen then infKindStar else freshKind()
      val tbinder' = unifyBinder(tb, rng, infgamma, resKind)
      if !isExtend then ()
      else
        val (_, kind) = findInfKind(newTp.name, newTp.range)
        with override val uctx = Check("extended type must have the same kind as the open type", newTp.range)
        unify(newTp.range, tbinder'.tbinderKind, kind)
      DataType(tbinder', infgamma, constrs', rng, vis, sort, ddef, isExtend, doc)

fun unifyBinder(tb: typeBinder<infKind>, rng: range, infgamma: list<typeBinder<infKind>>, resKind: infKind)
  val kind = infKindFunN(infgamma.map(tbinderKind), resKind)
  with override val uctx = Infer(rng)
  unify(rng, tb.tbinderKind, kind)
  tb

fun tbinderKind(TypeBinder(_, k, _, _): typeBinder<k>): k
  k

fun infConstr(UserCon(name, exists0, params, mbresult, rngName, rng, vis, doc): userCon<userType,userType,userKind>)
  val infgamma = exists0.map(bindTypeBinder)
  with extendInfGamma(infgamma)
  val params' = params.map(infConValueBinder)
  val result' = mbresult.map fn(t)
    with override val uctx = Check("Constructor results must be values", rng)
    infUserType(infKindStar, t)
  UserCon(name, infgamma, params', result', rngName, rng, vis, doc)

fun infConValueBinder((vis,ValueBinder(name, tp, mbExpr, nameRng, rng)): (visibility, valueBinder<userType, maybe<compiler/syntax/syntax/expr<userType>>>))
  with override val uctx = Check("Constructor parameters must be values", rng)
  val tp' = infUserType(infKindStar, tp)
  (vis, ValueBinder(name, tp', mbExpr, nameRng, rng))

fun infUserType(expected: infKind, userType: userType)
  match userType
    TpQuan(quant, tname, tp, r) ->
      val ikind = match quant
        QSome -> expected
        _ -> 
          unify(r, expected, infKindStar)
          expected
      val tname' = tname.bindTypeBinder
      with extendInfGamma([tname'])
      with checkQuant(r)
      val tp' = infUserType(ikind, tp)
      TpQuan(quant, tname', tp', r)
    TpQual(preds, tp) ->
      val r = userType.range
      with checkPred(r)
      val preds' = preds.map(fn(p) infUserType(KICon(kindPred), p))
      val tp' = infUserType(expected, tp)
      TpQual(preds', tp')
    TpFun(args, eff, tp, r) ->
      unify(r, expected, infKindStar)
      with checkArg(r)
      val args' = args.map(fn(a) infParam(infKindStar, a))
      // somewhat involved since we auto-wrap labels L into effects E here
      val ekind = freshKind()
      with checkEff(r)
      val etp = infUserType(ekind, eff)
      val skind = subst(ekind)
      val eff' = match skind
        KICon(k) | k == kindLabel -> makeEffectExtend(etp, makeEffectEmpty)
        KICon(k) | k == kindHandled -> makeEffectExtend(makeHandled(etp, r), makeEffectEmpty) // TODO: check if there is an effect declaration
        KICon(k) | k == kindHandled1 -> makeEffectExtend(makeHandled1(etp, r), makeEffectEmpty) // TODO: check if there is an effect declaration
        _ ->
          with checkEff(r)
          unify(r, KICon(kindEffect), skind)
          etp
      with checkRes(r)
      val tp' = infUserType(infKindStar, tp)
      TpFun(args', eff', tp', r)
    TpApp(tp as TpCon(nm), [lab, tl], r) | nm == nameEffectExtend ->
      with checkApp(r)
      val tp' = infUserType(infKindFunN([KICon(kindLabel), KICon(kindEffect)], expected), tp)
      with checkExtendTail(r)
      val tl' = infUserType(KICon(kindEffect), tl)
      // somewhat involved since we allow fixed effects to be used as labels
      // the append nodes are just used temporarily (see resolveApp in this file)
      val lkind = freshKind()
      with override val uctx = Infer(r)
      val ltp = infUserType(lkind, lab)
      val skind = subst(lkind)
      match skind
        KICon(kind) | kind == kindEffect -> makeEffectAppend(ltp, tl')
        KICon(kind) | kind == kindHandled ->
          // TODO: check effects environment if really effect?
          with checkExtendLabel(r)
          unify(r, KICon(kindHandled), skind)
          TpApp(tp', [makeHandled(ltp, r), tl'], r)
        KICon(kind) | kind == kindHandled1 ->
          // TODO: check effects environment if really effect?
          with checkExtendLabel(r)
          unify(r, KICon(kindHandled1), skind)
          TpApp(tp', [makeHandled1(ltp, r), tl'], r)
        _ ->
          with checkExtendLabel(r)
          unify(r, KICon(kindLabel), skind)
          TpApp(tp', [ltp, tl'], r)
    TpApp(tp, args, rng) ->
      val kinds = args.map(fn(_) freshKind())
      with checkApp(rng)
      val tp' = infUserType(infKindFunN(kinds, expected), tp)
      val args' = args.zip(kinds).map fn((arg, kind)) 
        with override val uctx = Infer(rng)
        infUserType(kind, arg)
      TpApp(tp', args', rng)
    TpVar(nm, rng) ->
      val (qname, kind) = findInfKind(nm, rng)
      unify(rng, expected, kind)
      TpVar(qname, rng)
    TpCon(nm, rng) ->
      val (qname, kind) = findInfKind(nm, rng)
      unify(rng, expected, kind)
      TpCon(qname, rng)
    TpParens(tp, rng) ->
      val tp' = infUserType(expected, tp)
      TpParens(tp', rng)
    TpAnn(tp, userKind) ->
      val rng = userType.range
      val kind = userKind.userKindToKind
      unify(rng, expected, kind)
      with checkAnnot(rng)
      val tp' = infUserType(kind, tp)
      TpAnn(tp', kind)

fun infParam(expected: infKind, (nm, tp): (name, userType))
  (nm, infUserType(expected, tp))

fun checkQuant(rng, f)
  with override val uctx = Check("Can only quantify over types", rng)
  f()

fun checkPred(rng, f)
  with override val uctx = Check("The left-hand side of a \"=>\" can only contain predicates", rng)
  f()

fun checkArg(rng, f)
  with override val uctx = Check("The parameters of a function type must be types", rng)
  f()

fun checkEff(rng, f)
  with override val uctx = Check("The effect of a function type must be an effect type", rng)
  f()

fun checkRes(rng, f)
  with override val uctx = Check("The result of a function type must be a type", rng)
  f()

fun checkAnnot(rng, f)
  with override val uctx = Check("The inferred kind doesn't match the annotated kind", rng)
  f()

fun checkApp(rng, f)
  with override val uctx = Check("The type cannot be applied to those arguments", rng)
  f()

fun checkExtendTail(rng, f)
  with override val uctx = Check("The extension of an effect must be an effect type", rng)
  f()

fun checkExtendLabel(rng, f)
  with override val uctx = Check("The elements of an effect must be effect constants", rng)
  f()

fun kindArity(kind: kind)
  match kind
    KApp(KApp(kcon, k1), k2) | kcon == kindArrow -> Cons(k1, kindArity(k2))
    _ -> []

// Resolve kinds: from InfKind to Kind, and UserType to Type
fun resolveTypeDef(isRec: bool, recNames: list<name>, td: compiler/syntax/syntax/typeDef<kUserType<infKind>, userType, infKind>)
  match td
    Synonym(syn, params, tp, rng, vis, doc) ->
      val syn' = syn.resolveTypeBinderDef
      val params' = params.map(resolveTypeBinder)
      val typeVars = params'.map(fn(p) freshTypeVar(p, Bound))
      val tvarMap = params'.map(name).zip(typeVars)
      val tp' = resolveType(tvarMap, True, tp)
      // eta-expand type synonyms
      val kind = syn'.typeBinderKind
      val arity = kind.arity
      val etaKinds = arity.drop(typeVars.length)
      val (etaTp, etaParams) = 
        if etaKinds.is-nil then
          (tp', typeVars)
        else
          val etaVars = etaKinds.map(fn(k) TypeVar(uniqueId("eta"), k, Bound))
          (typeApp(tp', etaVars.map(TVar)), typeVars ++ etaVars)
      addRangeInfo(rng, RIDecl("alias", syn'.name, syn.name.mangleTypeName))
      Synonym(SynInfo(syn'.name, syn.tBinderKind, etaParams, etaParams, etaTp, etaTp.maxSynonymRank + 1, rng, vis, doc))
    DataType(newtp, params, constrs, rng, vis, sort, ddef, isExtend, doc) ->
      val newtp' = 
        if isExtend then
          val (qname, ikind) = findInfKind(newTp.tbinderName, newTp.tbinderRange)
          val kind = ikind.resolveKind
          TypeBinder(qname, kind, newTp.tbinderNameRange, newTp.tbinderRange)
        else
          newTp.resolveTypeBinderDef
      val params' = params.map(resolveTypeBinder)
      val typeResult = TCon(TypeCon(newtp'.name, newtp'.tBinderKind))
      val typeVars =
        val (kargs, kres) = extractKindFun(newTp'.tBinderKind)
        if params.is-nil && !kargs.is-nil then
          kargs.map(fn(karg) TypeVar(uniqueId("k"), karg, Bound)) // invent parameters if they are not given (and it has an arrow kind)
        else
          params'.map(fn(p) freshTypeVar(p, Bound))
      val tvarMap = params'.map(name).zip(typeVars)
      val qname = newtp'.name
      val fname = qname.unqualify
      val name = if fname.isHandlerName then fname.fromHandlerName else fname
      val nameDoc = name.pretty.color(colors.colorType)
      val consinfos = constrs.map(fn(c) resolveConstructor(newtp'.name, sort, !ddef.isOpen, constrs.length == 1, typeResult, typeVars, tvarMap, c))
      val (constrs', conInfos0) = consinfos.unzip
      // check recursion
      if sort.is-retractive then
        ()
      else
        fun fromOpsName(nm: name)
          if nm.isOperationsName then [nm.fromOperationsName] else []
        val effNames = recNames.map(fromOpsName).concat
        if conInfos0.any(fn(ci) occursNegativeCon(recNames ++ effNames, ci)) then
          addError(rng, "Type".text |+| nameDoc |+| "is declared as being".text |-| "(co)inductive but it occurs recursively in a negative position.".text |-|
            " hint: declare it as a 'type rec' (or 'effect rec)' to allow negative occurences")
        else ()
      // create datadef and coninfos with correct ValueRepr and ordered fields
      fun emitError(d)
        addError(rng, "Type".text |+| nameDoc |+| d)
      fun emitWarning(d)
        addWarning(rng, "Type".text |+| nameDoc |+| d)
      val resultHasKindStar = typeResult.kind.hasKindStarResult
      val maxMembers = conInfos0.map(fn(ci) ci.params.length).maximum
      val conCount = conInfos0.length
      val willNeedStructTag = ddef.isValue && conCount > 1 && maxMembers >= 1
      val extraFields = 
        if ddef.isOpen then 1 // open datatype tag
        elif willNeedStructTag then 1 // explicit struct tag
        else 0
      val (ddef1, conInfos1) = createDataDef(emitError, emitWarning, lookupDataInfo, platform, qname, resultHasKindStar, isRec, sort, extraFields, ddef, conInfos)
      val dataInfo = DataInfo(sort, newtp'.name, newtp'.tBinderKind, typeVars, conInfos1, rng, ddef1, vis, doc)
      // TODO: Assertion
      addRangeInfo(rng, RIDecl(sort.show, newtp'.name, mangleTypeName(newtp'.name)))
      Data(dataInfo, isExtend)

fun occursNegativeCon(names: list<name>, ci: conInfo)
  val (_, _, rho) = ci.typeScheme.splitPredType
  match rho.splitFunType
    Just((pars, _, res)) -> pars.map(snd).any(fn(p) p.occursNegative(names)) || res.occursNegative(names)
    _ -> False

fun occursNegative(tp: ktype, names: list<name>)
  tp.occurs(names, False)

fun occurs(tp: ktype, names: list<name>, isNeg: bool)
  match tp
    TForAll(_, _, tp) -> tp.occurs(names, isNeg)
    TFun(args, eff, res) -> args.map(snd).any(fn(p) p.occurs(names, !isNeg)) || eff.occurs(names, !isNeg) || res.occurs(names, isNeg)
    TCon(tcon) -> if names.any(fn(n) n == tcon.name) then isNeg else False
    TVar -> False
    TApp(tp, args) -> Cons(tp, args).any(fn(t) t.occurs(names, isNeg))
    TSyn(_, _, t) -> t.occurs(names, isNeg)

fun showTypeBinder(TypeBinder(name, kind, _, _): typeBinder<kind>)
  name.show ++ ":" ++ kind.show

fun resolveTypeBinderDef(TypeBinder(name, infkind, rngName, rng): typeBinder<infKind>)
  val infkind' = infkind.resolveKind
  val qname = name.qualifyDef
  addRangeInfo(rngName, RIId(qname, NITypeCon(infkind'), True))
  TypeBinder(qname, infkind', rngName, rng)

fun resolveTypeBinder(TypeBinder(name, infkind, rngName, rng): typeBinder<infKind>)
  val infkind' = infkind.resolveKind
  addRangeInfo(rngName, RIId(name, NITypeCon(infkind'), True))
  TypeBinder(name, infkind', rngName, rng)

fun resolveKind(infkind: infKind)
  val skind = subst(infkind)
  fun resolve(k: infKind)
    match skind
      KIVar(_) -> kindStar // default unconstrained parameter to kind star
      KICon(k') -> k'
      KIApp(k1, k2) -> KApp(k1.resolve, k2.resolve)
  skind.resolve

val nameTVMapEmpty = linearMap([], fn(n1: name, n2: name) n1 == n2, fn(tv1: typeVar, tv2: typeVar) tv1 == tv2, show, show)

fun resolveConstructor(typeName: name, typeSort: dataKind, isSingleton: bool, typeResult: ktype, typeParams: list<typeVar>,
  idmap: name-map<typeVar>, UserCon(name, exists0, params, mbResult, rngName, rng, vis, doc): userCon<kUserType<infKind>, userType, infKind>)
  val qname = name.qualifyDef
  val exist' = exists0.map(resolveTypeBinder)
  val existVars = exist'.map(fn(e) freshTypeVar(e, Bound))
  val idmap' = (nameTVMapEmpty + exist'.map(name).zip(existVars)).union(idmap) // assume left biased union 
  val params' = params.map(fn(p) resolveConParam(p, idmap'))
  val result = match mbResult
    Nothing -> TypeApp(typeResult, typeParams.map(TVar))
    Just(tp) -> resolveType(idmap', False, tp)
  val scheme = quantifyType(typeParams ++ existVars, if params'.is-nil then result else TypeFun(params'.map(fn((_, p)) (p.binderName, p.binderType)), typeTotal, result))
  addRangeInfo(rng, RIDecl("con", qname, qname.mangleConName))
  addRangeInfo(rngName, RIId(qname, NICon(scheme), True))
  val fields = params'.map(snd).map-indexed(fn(i, b) (if b.binderName.isNil then (i + 1).newFieldName else b.binderName, b.binderType))
  (UserCon(qname, exist', params', Just(result), rngName, rng, vis, doc), 
  ConInfo(qname, typeName, typeParams, existVars, fields, scheme, typeSort, rngName, 
    params'.map(fn((_, b)) b.nameRange), params'.map(fst), isSingleton, [], valueReprZero // Initialized later at the datadef
    , vis, doc))

fun resolveConParam(idmap: name-map<typeVar>, (vis, ValueBinder(name, tp, mbExpr, nameRng, rng)): (visibility, valueBinder<kUserType<infKind>, maybe<compiler/syntax/syntax/expr<userType>>>))
  val tp' = resolveType(idmap, False, tp)
  val expr = match mbExpr
    Nothing -> Nothing
    Just(e) -> Just(fail("kind/infer/resolveConParam: optional parameter expression in constructor"))
  addRangeInfo(nameRng, RIId(name, NIValue(tp'), True))
  (vis, ValueBinder(name, tp', expr, nameRng, rng))

// resolveType takes: a map from locally quantified type name variables to types,
// a boolean that is 'True' if partially applied type synonyms are allowed (i.e. when
// these are arguments to type synonyms themselves), a user type with inference kinds,
// and it returns a fully resolved type
fun resolveType(idmap: name-map<typeVar>, partialSyn: bool, userType: kUserType<infKind>)
  fun resolveParam((nm, tp): (name, kUserType<infKind>))
    (nm, resolveType(idmap, False, tp))
  fun collectArgs(args: list<kUserType<k>>, tp: kUserType<k>): (kUserType<k>, list<kUserType<k>>)
    match tp
      TpApp(tp', args') -> collectArgs(args' ++ args, tp')
      TpParens(tp') -> collectArgs(args, tp')
      TpAnn(tp') -> collectArgs(args, tp')
      _ -> (tp, args)
  match userType
    TpQuan(QForall, tname, tp) ->
      val tname' = tname.resolveTypeBinder
      val tvar = freshTypeVar(tname', Bound)
      val tp' = resolveType(idmap.set(tname.name, tvar), False, tp)
      quantifyType([tvar], tp')
    TpQuan(QSome, tname, tp) ->
      val tname' = tname.resolveTypeBinder
      val tvar = freshTypeVar(tname', Meta)
      val tp' = resolveType(idmap.set(tname.name, tvar), False, tp)
      tp'
    TpQuan(QExists) ->
      fail("kind/infer resolveType: existentials are not supported yet")
    TpQual(preds, tp) ->
      val preds' = preds.map(fn(p) resolvePredicate(idmap, p))
      val tp' = resolveType(idmap, False, tp)
      qualifyType(preds', tp')
    TpFun(args, eff, tp) ->
      val args' = args.map(resolveParam)
      val eff' = resolveType(idmap, False, eff)
      val tp' = resolveType(idmap, False, tp)
      TFun(args', eff', tp')
    TpApp(tp, args, rng) ->
      resolveApp(idmap, partialSyn, args.collectArgs(tp), rng)
    TpVar(_, rng) ->
      resolveApp(idmap, partialSyn, (userType, []), rng)
    TpCon(_, rng) ->
      resolveApp(idmap, partialSyn, (userType, []), rng)
    TpParens(tp) ->
      resolveType(idmap, partialSyn, tp)
    TpAnn(tp) ->
      resolveType(idmap, partialSyn, tp)

fun resolvePredicate(idmap: name-map<typeVar>, tp: kUserType<infKind>)
  val tp' = resolveType(idmap, False, tp)
  match tp'
    TApp(TCon(tc), targs) -> PredIFace(tc.name, targs)
    TCon(tc) -> PredIFace(tc.name, [])
    _ -> fail("kind/infer resolvePredicate: invalid predicate: " ++ tp'.show)

fun resolveApp(idmap: name-map<typeVar>, partialSyn: bool, (tp, args): (kUserType<infKind>, list<kUserType<infKind>>), rng: range)
  match (tp, args)
    (TpVar(name, r), _) ->
      val (tp', kind) = match idmap.maybeGet(name)
        Nothing ->
          addError("Type variable".text |+| name.pretty.color(colors.colorType) |+| "is undefined".text |-|
            " hint: bind the variable using".text |+| ("forall<".text |.| name.pretty |.| ">".text).color(colors.colorType), rng)
          (TVar(TypeVar(name.show.uniqueId, kindStar, Bound)), kindStar)
        Just(tvar) -> (TVar(tvar), tvar.kind)
      if !name.isImplicitTypeVarName then
        addRangeInfo(r, RIId(name, NITypeVar(kind), False))
      val args' = args.map(fn(a) resolveType(idmap, False, a))
      TApp(tp', args')
    (TpCon(name), [fixed, ext]) | name == nameEffectAppend ->
      val fixed' = resolveType(idmap, False, fixed)
      val ext' = resolveType(idmap, False, ext)
      val (_, tl) = fixed'.extractOrderedEffect
      if !tl.isEffectEmpty then
        addError("Effects can only have one extension point (use a `|` instead of a comma in the effect type ?)".text, rng)
      (fixed'.shallowEffectExtend(ext'))
    (TpCon(nm, r), _) ->
      val (qname, ikind) = findInfKind(nm, rng)
      val k = ikind.resolveKind
      addRangeInfo(r, RIId(qname, NITypeCon(k), False))
      val mbSyn = infKindEnv.synonyms.synonymsLookup(nm)
      match mbSyn
        Just(syn as SynInfo(name, kind, params, tp', rank)) ->
          // check over/under application
          if !partialSyn && args.length < params.length then
            addError("Type alias".text |+| name.pretty.color(colors.colorType) |+| "is not fully applied".text |-|
              " hint: add more type arguments".text, rng)
          elif args.length > params.length then
            addError("Type alias".text |+| name.pretty.color(colors.colorType) |+| "is over-applied".text |-|
              " hint: remove some type arguments".text, rng)
          else ()
          val args' = args.map(fn(a) resolveType(idmap, False, a)) // partially applied synonyms are allowed in synonym applications
          val tsyn = TSyn(TypeSyn(name, kind, rank, Just(syn)), args', params.zip(args').subNew |-> tp')
          tsyn
          // NOTE: on partially applied type synonyms, we geet a funky body type with free parameters but this
          // is only inside synonyms arguments so we are ok
        Nothing ->
          TApp(TCon(TypeCon(nm, k)), args.map(fn(a) resolveType(idmap, False, a)))
    _ -> fail("kind/infer resolveApp: this case should never occur after kind checking")

fun makeEffectAppend(fixed, ext)
  TpApp(TpCon(nameEffectAppend, rangeNull), [fixed, ext], rangeNull)

fun makeEffectExtend(label, ext)
  TpApp(TpCon(nameEffectExtend, rangeNull), [label, ext], rangeNull)

val makeEffectEmpty =
  TpCon(nameEffectEmpty, rangeNull)

fun makeHandled(u, rng)
  TpApp(TpCon(nameTpHandled, rangeNull), [u], rangeNull)

fun makeHandled1(u, rng)
  TpApp(TpCon(nameTpHandled1, rangeNull), [u], rangeNull)

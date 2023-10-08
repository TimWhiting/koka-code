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
import compiler/core/core = core
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
    addError("Type synonyms cannot be recursive".text, tdefs.getRange)

// Setup type environment for recursive definitions
fun bindTypeDef(tdef: compiler/syntax/syntax/typeDef<userType, userType, userKind>)
  val TypeBinder(name, kind, rngName, rng) = bindTypeBinder(tdef.binder)
  val qname = if isExtend then name else name.qualifyDef
  val isExtend = 
    match tdef
      DataType(isExtend=yes) -> yes
      _ -> False
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
    External(name, tp, pinfos, nameRng, rng, calls, vis, fipT, doc) ->
      with uctx = Check("Externals must be values", rng)
      val tp' = tp.infResolveType()
      val qname = name.qualifyDef
      val cname = canonicalName(names.filter(fn(n) n == qname).length, qname)
      if name.isHiddenName then ()
      else
        addRangeInfo(nameRng, Id(qname, NIValue(tp'), True))
        addRangeInfo(rng, Decl("external", qname, cname.mangle(tp')))
      (compiler/core/core/External(cname, tp', pinfos, calls.map(fn(c) c.formatCall(tp')), vis, fipT, nameRng, doc), Cons(qname, names))
    _ -> (ex, names)

fun formatCall((target, externalCall): (target, externalCall), tp: ktype)
  match externalCall
    ExternalInline -> (target, externalCall)
    ExternallCall(fname) ->
      val (foralls, _, rho) = tp.splitPredType
      val argumentCount = match rho.splitFunType
        Just((args, _, _)) -> args.length
        _ -> 0
      val arguments = "(" ++ list(1, argumentCount.length).map(fn(i) "#" ++ i.show).join(",") ++ ")"
      val argumentsC = "(" ++ list(1, argumentCount.length).map(fn(i) "#" ++ i.show).join(",") ++ (if fname.starts-with("kk_").is-just then "kk_context()" else "") ++ ")"
      val typeArguments = if foralls.is-nil then "" else "<" ++ list(1, foralls.length).map(fn(v) "##" ++ v.show).join(",") ++ ">"
      match target
        CS -> (target, fname ++ typeArguments ++ arguments)
        JS -> (target, fname ++ arguments)
        C -> (target, fname ++ argumentsC)
        DefaultTarget -> (target, fname ++ arguments)

// TODO: Lots more
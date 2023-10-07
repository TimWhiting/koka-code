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
    Data(_) -> []
      // di.synAccessors(modName) // TODO:

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

// TODO: Lots more
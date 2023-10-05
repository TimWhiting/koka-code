import compiler/common/name
import compiler/common/name-collections
import compiler/common/range
import compiler/common/syntax
import compiler/syntax/syntax
import compiler/lib/scc
import newstd/data/linearset
import newstd/data/linearmap

// Program
fun bindingGroups(program: userProgram)
  program(typeDefs=bindingsTypeDefs(program.typeDefs), defs=defs.bindings(modName))

// Binding groups in type definitions
fun bindingsTypeDefs(tdGroups: list<userTypeDefGroup>)
  val (ds, extends) = tdGroups.flatten.partition(isDefinition)
  ds.groupTypeDefs(ds.map(dependencyTypeDef)) ++ extends.map(TypeDefNonRec)

fun flatten(grps: list<userTypeDefGroup>)
  val xs = grps.map fn(g)
    match g
      TypeDefRec(tds) -> tds
      TypeDefNonRec(td) -> [td]
  xs.concat

fun isDefinition(td: userTypeDef)
  match td
    DataType(isExtend=False) -> True
    _ -> True

fun dependencyTypeDef(td: userTypeDef)
  match td
    Synonym(_, _, t) -> (td.typeDefName, t.freeTypes)
    DataType(_, _, c) -> (td.typeDefName, c.map(fn(c') c'.freeTypes(freeTypes)).unions)

// Free type constructors
fun freeTypes(l: list<kUserType<k>>): pure nameSet
  l.map(fn(t) t.freeTypes).unions

fun freeTypes(tp: kUserType<k>): pure nameSet
  match tp
    TpQuan(_, _, t) -> t.freeTypes
    TpQual(preds, t) -> Cons(t, preds).freeTypes
    TpFun(args, eff, t) -> args.map(snd).freeTypes + eff.freeTypes + t.freeTypes
    TpApp(t, args) -> Cons(t, args).freeTypes
    TpVar -> namesEmpty
    TpCon(nm) -> namesEmpty + nm
    TpParens(t) -> t.freeTypes
    TpAnn(t) -> t.freeTypes

fun freeTypes(vb: valueBinder<t,e>, freeTypesT: (t) -> pure nameSet): pure nameSet
  vb.binderType.freeTypesT

fun freeTypes(vbs: list<valueBinder<t,e>>, freeTypesT: (t) -> pure nameSet): pure nameSet
  vbs.map(fn(vb) vb.freeTypes(freeTypesT)).unions

fun freeTypes(c: userCon<t,u,k>, freeTypesT: (t) -> pure nameSet): pure nameSet
  c.params.map(snd).freeTypes(freeTypesT) + c.result.map(fn(r) r.freeTypesT).default(namesEmpty)

// Binding groups in definitions
fun bindings(dgs: list<userDefGroup>, modName: name)
  val (defs, deps) = dgs.map(fn(dg) dg.bindingsDefGroup(modName)).unzip
  group(defs.concat, deps.unions)

fun bindingsDefGroup(g: userDefGroup, modName: name)
  match g
    DefNonRec(d) ->
      val (d', deps) = d.dependencyDef(modName)
      ([d'], deps)
    DefRec(defs) -> defs.dependencies(modName)

fun dependencies(defs: list<userDef>, modName: name)
  val (defDefs, depss) = defs.map(fn(d) d.dependencyDef(modName)).unzip
  val deps = depss.unions
  val freeVars = deps.map(snd).unions
  val defVars = deps.map(fst)
  (depDefs, deps)

fun dependencyDef(d: userDef, modName: name)
  val (depBinding, deps) = d.binder.dependencyBinding(modName)
  (d(binder=depBinding), deps)

fun dependencyBinding(vb: userValueBinder<userExpr>, modName: name)
  val (depExpr, freeVar) = vb.expr.dependencyExpr(modName)
  (vb(expr=depExpr), emptyDeps.add(vb.name, freeVar))


// TODO:




// Dependencies
alias deps = name-map<nameSet>
alias freeVar = nameSet
val emptyDeps = linearMap([], fn(x1:name, x2) x1 == x2, fn(y1:nameSet, y2) y1 == y2, fn(x) x.show, fn(y) y.show)

// Topological sort

// TODO:
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
  program(typeDefs=bindingsTypeDefs(program.typeDefs), defs=program.defs.bindings(program.name))

// Binding groups in type definitions
fun bindingsTypeDefs(tdGroups: list<userTypeDefGroup>)
  val (ds, extends) = tdGroups.flatten.partition(isDefinition)
  ds.groupTypeDefs(emptyDeps.addAll(ds.map(dependencyTypeDef))) ++ extends.map(TypeDefNonRec)

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

fun dependencyTypeDef(td: userTypeDef): pure (name, nameSet)
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

fun bindingsDefGroup(g: userDefGroup, modName: name): pure (list<userDef>, deps)
  match g
    DefNonRec(d) ->
      val (d', deps) = d.dependencyDef(modName)
      ([d'], deps)
    DefRec(defs) -> 
      defs.dependencies(modName)

fun dependencies(defs: list<userDef>, modName: name): pure (list<userDef>, deps)
  val (defDeps, depss) = defs.map(fn(d) d.dependencyDef(modName)).unzip
  (defDeps, depss.unions)

fun dependencyDef(d: userDef, modName: name): pure (userDef, deps)
  val (depBinding, deps) = d.binder.dependencyBinding(modName)
  (d(binder=depBinding), deps)

fun dependencyBinding(vb: userValueBinder<userExpr>, modName: name)
  val (depExpr, freeVar) = vb.expr.dependencyExpr(modName)
  (vb(expr=depExpr), emptyDeps.add(vb.name, freeVar))

fun dependencyDefFv(d: userDef, modName: name): pure (userDef, nameSet)
  val (depDef, deps) = d.dependencyDef(modName)
  (depDef, deps.list.map(snd).unions)

fun dependencyDefGroupFv(dg: userDefGroup, modName: name)
  val (defs, deps) = dg.bindingsDefGroup(modName)
  val names = defs.map(fn(d:userDef) d.binder.name)
  val freeVars = deps.list.map(snd).unions - names
  (defs.group(deps), freeVars, names)

fun dependencyExpr(mex: maybe<userExpr>, modName: name): pure (maybe<userExpr>, nameSet)
  match mex
    Just(ex) ->
      val (ex', deps) = ex.dependencyExpr(modName)
      (Just(ex'), deps)
    Nothing -> (Nothing, namesEmpty)

fun dependencyExpr(ex: userExpr, modName: name): pure (userExpr, nameSet)
  match ex
    Lam(binders, body, rng) ->
      val (depBody, fv1) = body.dependencyExpr(modName)
      val (binders', fv2) = binders.dependencyLamBinders(modName, fv1)
      (Lam(binders', depBody, rng), fv2)
    Bind(def, body, rng) ->
      val (depDef, fv1) = def.dependencyDefFv(modName)
      val (depBody, fv2) = body.dependencyExpr(modName)
      (Bind(depDef, depBody, rng), fv1 + (fv2 - def.def-name))
    Let(group, body, rng) ->
      val (depGroups, fv1, names) = group.dependencyDefGroupFv(modName)
      val (depBody, fv2) = body.dependencyExpr(modName)
      (depGroups.foldr(depBody, fn(g, l) Let(g, l, rng)), fv1 + (fv2 - names))
    Var(name) ->
      if name.isConstructorName then
        (ex, namesEmpty + name + name.newCreatorName)
      else
        (ex, namesEmpty + name + name.toValueOperationName)
    App(f, nargs, rng) ->
      val (depF, fv1) = f.dependencyExpr(modName)
      val (argNames, args) = nargs.unzip
      val (depArgs, fv2s) = args.map(fn(a) a.dependencyExpr(modName)).unzip
      val fv2 = fv2s.unions
      (App(depF, argNames.zip(depArgs), rng), fv1 + fv2)
    Ann(e, t, rng) ->
      val (depE, fv1) = e.dependencyExpr(modName)
      (Ann(depE, t, rng), fv1)
    Case(e, brnches, rng) ->
      val (depE, fv1) = e.dependencyExpr(modName)
      val (depBranches, fv2) = brnches.map(fn(b) b.dependencyBranch(modName)).unzip
      (Case(depE, depBranches, rng), fv1 + fv2.unions)
    Parens(e, nm, rng) ->
      val (depE, fv) = e.dependencyExpr(modName)
      (Parens(depE, nm, rng), fv)
    Literal ->
      (ex, namesEmpty)
    Handler(shallow, scoped, over, allowMask, eff, pars, reinit, ret, fin, ops, hrng, rng) ->
      val (depRet, fv1) = ret.dependencyExpr(modName)
      val (depBranches, fv2) = ops.map(fn(b) b.dependencyHandlerBranch(modName)).unzip
      val (depReinit, fv3) = reinit.dependencyExpr(modName)
      val (depFin, fv4) = fin.dependencyExpr(modName)
      val fvs = (fv1 + fv2.unions + fv3 + fv4) - (namesEmpty + pars.map(name))
      (Handler(shallow, scoped, over, allowMask, eff, pars, depReinit, depRet, depFin, depBranches, hrng, rng), fvs)
    Inject(tp, body, b, rng) ->
      val (depBody, fv) = body.dependencyExpr(modName)
      (Inject(tp, depBody, b, rng), fv)

fun dependencyHandlerBranch(h: userHandlerBranch, modName: name): pure (userHandlerBranch, nameSet)
  val (depExpr, fvExpr) = h.branchExpr.dependencyExpr(modName)
  val uname = if h.branchName.qualifier == modName then h.branchName.unqualify else h.branchName
  (h(branchExpr=depExpr), (fvExpr - h.branchPars.map(name)) + uname)

fun dependencyBranch(Branch(patts, guards): userBranch, modName: name): pure (userBranch, nameSet)
  val (depGuards, fvGuardss) = guards.map(fn(g) g.dependencyGuard(modName)).unzip
  (Branch(patts, depGuards), fvGuardss.unions - patts.freeVar)

fun dependencyGuard(Guard(test, expr): userGuard, modName: name)
  val (depTest, fv1) = test.dependencyExpr(modName)
  val (depExpr, fv2) = expr.dependencyExpr(modName)
  (Guard(depTest, depExpr), fv1 + fv2)

fun dependencyLamBinders(binders: list<valueBinder<maybe<userType>, maybe<userExpr>>>, modName: name, fvs: nameSet)
  match binders
    Nil -> (Nil, fvs)
    Cons(binder, rest) ->
      val (binders0, fv0) = rest.dependencyLamBinders(modName, fvs)
      val fv1 = fv0 - binder.name
      match binder.expr
        Nothing -> (Cons(binder, binders0), fv1)
        Just(ex) ->
          val (depEx, fv2) = ex.dependencyExpr(modName)
          (Cons(binder(expr=Just(depEx)), binders0), fv1 + fv2)

fun dependencyLamBinder(binder: valueBinder<maybe<userType>, maybe<userExpr>>, modName: name)
  match binder.expr
    Nothing -> (binder, namesEmpty)
    Just(ex) ->
      val (depEx, fv) = ex.dependencyExpr(modName)
      (binder(expr=Just(depEx)), fv)


// Free variables
fun freeVar(pat: pattern<t>): pure nameSet
  match pat
    PatVar(binder) -> namesEmpty + binder.name
    PatCon(_, pats) -> pats.map(snd).map(freeVar).unions
    PatParens(p) -> p.freeVar
    PatAnn(p, _) -> p.freeVar
    PatLit(_) -> namesEmpty
    PatWild -> namesEmpty

fun freeVar(pats: list<pattern<t>>): pure nameSet
  pats.map(freeVar).unions

fun freeVar(exs: list<expr<t>>): pure nameSet
  exs.map(freeVar).unions

fun freeVar(mex: maybe<expr<t>>): pure nameSet
  match mex
    Just(ex) -> ex.freeVar
    Nothing -> namesEmpty

fun freeVar(ex: expr<t>): pure nameSet
  match ex
    Lam(binders, body) -> binders.foldr(body.freeVar, fn(b, fv) fv - b.name)
    Bind(def, body) -> body.freeVar - def.def-name + def.def-body.freeVar
    Let(group, body) ->
      val (fv, bound) = group.freeBoundVar
      body.freeVar - bound + fv
    Var(name) -> if name.isConstructorName then namesEmpty else namesEmpty + name
    App(f, nargs) -> Cons(f, nargs.map(snd)).freeVar
    Ann(e) -> e.freeVar
    Case(e, brnches) -> e.freeVar + brnches.map(freeVar).unions
    Parens(e) -> e.freeVar
    Literal -> namesEmpty
    Inject(_, body) -> body.freeVar
    Handler(branches=ops, hReturn=ret, initially=init, finally=fin, localPars=pars) ->
      ret.freeVar + ops.map(freeVar).unions + init.freeVar + fin.freeVar - pars.map(name)

fun freeVar(Branch(patt, guards): branch<t>): pure nameSet
  patt.freeVar + guards.map(freeVar).unions

fun freeVar(Guard(test, expr): guard<t>): pure nameSet
  test.freeVar + expr.freeVar

fun freeVar(HandlerBranch(_, pars, expr): handlerBranch<t>): pure nameSet
  expr.freeVar - pars.map(name)

fun freeBoundVar(dg: defGroup<t>): pure (nameSet, nameSet)
  match dg
    DefNonRec(d) -> (namesEmpty + d.def-name, d.def-body.freeVar)
    DefRec(defs) ->
      val bound = defs.map(def-name)
      val free = defs.map(fn(d) d.def-body.freeVar).unions
      (namesEmpty + bound, free - bound)

// Dependencies
alias deps = name-map<nameSet>
alias freeVar = nameSet
val emptyDeps: linearMap<name, nameSet> = linearMap([], fn(x1:name, x2) x1 == x2, fn(y1:nameSet, y2) y1 == y2, fn(x) x.show, fn(y) y.show)

// Topological sort

fun group(defs: list<userDef>, deps: deps): pure list<userDefGroup>
  // get definition id's
  val defVars = namesEmpty + deps.list.map(fst)
  // constrain to the current group of id's
  val defDeps0 = deps.list.map(fn((k, fvs)) (k, fvs.intersection(defVars).list))
  // determine strongly connected components
  val defOrder0 = scc(defDeps0, fn(n1, n2) n1 == n2, fn(n) n.show)
  val defOrder =
    fun noDeps(ids: list<name>)
      match ids
        [id] -> id.isEarlyBindName || defDeps0.find(fn((i, _)) i == id).map(fn((_, r)) r.is-nil).default(False)
        _ -> False
    val (xs, ys) = defOrder0.partition(noDeps) // no dependencies first
    fun isHidden(ids: list<name>)
      match ids
        [id] -> id.isHiddenName
        _ -> False
    val (xxs, xys) = xs.partition(isHidden) // and hidden names first inside those
    xxs ++ xys ++ ys
  // create a map from definition id's to definitions
  val defMap = defs.map(fn(d) (d.def-name, [d])).foldl(linearMap([], fn(n1:name, n2) n1 == n2, fn(d1: list<userDef>, d2: list<userDef>) False, fn(n) n.show, fn(u) "")) fn(acc, (id, v))
    acc.update(id, v, fn(old:list<userDef>, new) old ++ new)
  // create a definition group from a list of mutal recursive identifiers
  fun makeGroup(ids:list<name>)
    match ids
      [id] -> 
        if defDeps0.find(fn((k, _)) k == id).map(snd).default([]).any(fn(i) i == id) then
          [DefRec(defMap.get(id))]
        else
          defMap.get(id).map(DefNonRec)
      _ -> [DefRec(ids.map(fn(id) defMap.get(id)).concat)]
  defOrder.map(makeGroup).concat

fun groupTypeDefs(tdefs: list<userTypeDef>, deps: deps)
  // get type names
  val typeNames = namesEmpty + deps.list.map(fst)
  // constrain to current group of ids
  val typeDeps0 = deps.list.map(fn((k, fts)) (k, fts.intersection(typeNames).list))
  // determine strongly connected components
  val typeOrder0 = scc(typeDeps0, fn(n1, n2) n1 == n2, fn(n) n.show)
  // create a map from type id's to type defs
  // note: due to duplicate definitions (which are checked for during kind checking), we map to a list of possible definitions
  val typeMap = tdefs.map(fn(d) (d.typeDefName, [d])).foldl(linearMap([], fn(n1:name, n2) n1 == n2, fn(d1: list<userTypeDef>, d2: list<userTypeDef>) False, fn(n) n.show, fn(u) "")) fn(acc, (id, v))
    acc.update(id, v, fn(old:list<userTypeDef>, new) old ++ new)
  // create a (recursive) definition group
  fun makeGroup(ids: list<name>)
    match ids
      [id] ->
        if typeDeps0.find(fn((k, _)) k == id).map(snd).default([]).any(fn(i) i == id) then
          [TypeDefRec(typeMap.get(id))]
        else
          typeMap.get(id).map(TypeDefNonRec)
      _ -> [TypeDefRec(ids.map(fn(id) typeMap.get(id)).concat)]
  typeOrder0.map(makeGroup).concat

    

// As a tribute to Doaitse Swierstra, let's leave in this code which
// was from a time when we used the Attribute Grammar system from
// Doaitse developed at the University of Utrecht.

// {--------------------------------------------------------------------
//   Group
// --------------------------------------------------------------------}
// ATTR Program TypeDefs TypeDef Def Defs Expr Pattern Lit
//      Exprs Patterns Branch Branches
//      UserType UserTypes UserKindScheme UserKind
//      Externals External
//      FixDefs FixDef
//       [ || grouped : SELF ]


// ATTR DefGroup  [ || grouped : DefGroups]
// ATTR DefGroups [ || grouped USE {++} {[]}: DefGroups]

// SEM DefGroup
//   | DefNonRec lhs.grouped = [DefNonRec @def.grouped]
//   | DefRec    lhs.grouped = group @defs.grouped @defs.deps


// ATTR TypeDefGroup  [ || grouped : TypeDefGroups]
// ATTR TypeDefGroups [ || grouped USE {++} {[]}: TypeDefGroups]

// SEM TypeDefGroup
//   | TypeDefGroup lhs.grouped = groupTypeDefs @typeDefs.grouped @typeDefs.deps


// {
// group :: Defs -> Deps -> DefGroups
// group defs deps
//   = let -- get definition id's
//         defVars  = S.fromList (M.keys deps)
//         -- constrain to the current group of id's
//         defDeps  = M.map (\fvs -> S.intersection defVars fvs) deps
//         -- determine strongly connected components
//         defOrder = scc [(id,S.toList fvs) | (id,fvs) <- M.toList defDeps]
//         -- create a map from definition id's to definitions.
//         defMap   = M.fromList [(def-name def,def) | def <- defs]
//         -- create a definition group from a list of mutual recursive identifiers.
//         makeGroup ids  = case ids of
//                            [id] -> if S.member id (M.find id defDeps)
//                                     then DefRec [M.find id defMap]
//                                     else DefNonRec (M.find id defMap)
//                            _    -> DefRec [M.find id defMap | id <- ids]
//     in map makeGroup defOrder

// groupTypeDefs :: TypeDefs -> Deps -> TypeDefGroups
// groupTypeDefs typeDefs deps
//   = let -- get type names
//         typeNames = S.fromList (M.keys deps)
//         -- constrain to current group of id's
//         typeDeps  = M.map (\fts -> S.intersection typeNames fts) deps
//         -- determine strongly connected components
//         typeOrder = scc [(id,S.toList fts) | (id,fts) <- M.toList typeDeps]
//         -- create a map from type id's to type defs
//         typeMap   = M.fromList [(typeDefName def,def) | def <- typeDefs]
//         -- create a (recursive) definition group
//         makeGroup ids = TypeDefGroup [M.find id typeMap | id <- ids]
//     in map makeGroup typeOrder
// }

// {
// --------------------------------------------------------------------
//   Dependencies
// --------------------------------------------------------------------}
// {
// type Deps = M.NameMap S.NameSet
// }

// ATTR TypeDef TypeDefs Def Defs [ || deps USE {`M.union`} {M.empty} : Deps ]

// SEM Def
//   | Def   lhs.deps  = M.single @name @body.freeVar

// SEM TypeDef
//   | Synonym lhs.deps = M.single @name @tp.freeTypes
//   | Newtype lhs.deps = M.single @name @tp.freeTypes

// {--------------------------------------------------------------------
//   Free variables (and defined variables)
// --------------------------------------------------------------------}
// ATTR DefGroups DefGroup Defs Def Expr Exprs Branch Branches    [ || freeVar USE {`S.union`}{S.empty} : {S.NameSet} ]
// ATTR DefGroups DefGroup Defs Def Pattern Patterns  [ || defVar USE {`S.union`}{S.empty} : {S.NameSet} ]

// SEM DefGroup
//   | DefRec    lhs.freeVar = S.difference @defs.freeVar @defs.defVar
//   | DefNonRec lhs.freeVar = S.difference @def.freeVar @def.defVar     -- paranoia :-)

// SEM Def
//   | Def     lhs.defVar  = S.single @name

// SEM Expr
//   | Lam     lhs.freeVar = S.difference @body.freeVar @pat.defVar
//   | Let     lhs.freeVar = S.union @defs.freeVar (S.difference @body.freeVar @defs.defVar)
//   | Var     lhs.freeVar = S.single @name

// SEM Branch
//   | Branch  lhs.freeVar = S.difference (S.union @guard.freeVar @expr.freeVar) @pats.defVar

// SEM Pattern
//   | PatVar  lhs.defVar  = S.single @name

// {--------------------------------------------------------------------------
//   Free types
// --------------------------------------------------------------------------}
// ATTR UserTypes UserType [ || freeTypes USE {`S.union`} {S.empty} : {S.NameSet} ]

// SEM UserType
//   | TpCon       lhs.freeTypes = S.single @name
import compiler/core/core
import newstd/data/linearset
import compiler/common/name
import compiler/type/typevar

pub infixr 5 (|->)

fun isTopLevel(d: def)
  val freeVar = d.defExpr.freeVars.list.map(fn(TName(nm)) nm).filter(fn(nm) !nm.isQualified && d.def-name.unqualify != nm)
  val freeTv = d.defExpr.free-type-vars
  freeVar.is-nil && freeTv.is-empty

fun freeLocals(e: expr)
  e.freeVars.filter(fn(TName(nm)) !nm.isQualified)

fun freeLocals(b: branch)
  b.freeVars.filter(fn(TName(nm)) !nm.isQualified)

fun freeVars(l: list<expr>): pure linearSet<tName>
  l.map(freeVars).unions

fun freeVars(e0: expr): pure linearSet<tName>
  match e0
    Lam(tnames, _, e) -> e.freeVars - tnames
    Var(tn) -> tnamesEmpty + tn
    App(e1, e2) -> e1.freeVars + e2.freeVars
    TypeLam(_, e) -> e.freeVars
    TypeApp(e) -> e.freeVars
    Con -> tnamesEmpty
    ELit -> tnamesEmpty
    Let(dfgps, e) -> freeVars(dfgps, e)
    Case(exprs, bs) -> exprs.freeVars + bs.map(freeVars).unions

fun freeVars(Branch(patterns, guards): branch): pure linearSet<tName>
  guards.map(freeVars).unions - patterns.map(boundVars).unions

fun freeVars(Guard(test, expr): guard): pure linearSet<tName>
  test.freeVars + expr.freeVars

fun boundVars(p: pattern): pure linearSet<tName>
  match p
    PatCon(_, args) -> args.map(boundVars).unions
    PatVar(tn) -> tnamesEmpty + tn
    PatLit -> tnamesEmpty
    PatWild -> tnamesEmpty

fun freeVars(defGroups: defGroups, e: expr): pure linearSet<tName>
  match defGroups
    [] -> e.freeVars
    Cons(dg, dgs) -> 
      val fv1: linearSet<tName> = (freeVars(dgs, e) - dg.boundVars)
      dg.freeVars + fv1

fun freeVars(defg: defGroup): pure linearSet<tName>
  defg.flatten.map(freeVars).unions

fun boundVars(defg: defGroup): pure linearSet<tName>
  defg.flatten.map(boundVars).unions

fun boundVars(Def(nm, tp): def): pure linearSet<tName>
  tnamesEmpty + TName(nm, tp)

fun freeVars(Def(_, _, e): def): pure linearSet<tName>
  e.freeVars

// Term substitutions
fun (|->)(sub: list<(tName, expr)>, l: list<a>, ?s: (list<(tName, expr)>, a) -> pure a = (|->)): pure list<a>
  l.map(fn(x) s(sub, x))

fun (|->)(sub: list<(tName, expr)>, dg: defGroup): pure defGroup
  match dg
    DefRec(defs) -> DefRec(sub |-> defs)
    DefNonRec(def) -> DefNonRec(sub |-> def)

fun (|->)(sub: list<(tName, expr)>, d: def): pure def
  val dname = d.def-name
  val sub' = sub.filter(fn((nm, _)) nm.getName != dname)
  d(defExpr = sub' |-> d.defExpr)

fun (|->)(sub: list<(tName, expr)>, ex: expr): pure expr
  match ex
    Lam(tnames, eff, expr) ->
      val sub' = sub.filter(fn((nm, _)) !tnames.any(fn(n) n == nm))
      Lam(tnames, eff, sub' |-> expr)
    Var(tn, _) -> sub.lookup(fn(n) n == tn).default(ex)
    App(e1, e2) -> App(sub |-> e1, sub |-> e2)
    TypeLam(tvs, e) -> TypeLam(tvs, sub |-> e)
    TypeApp(e, tp) -> TypeApp(sub |-> e, tp)
    Con -> ex
    ELit -> ex
    Let(dgs, e) ->
      val defnames = dgs.flatten.map(def-name)
      val sub' = sub.filter(fn((nm, _)) !defnames.any(fn(n) n == nm.getName))
      Let(sub' |-> dgs, sub' |-> e)
    Case(exprs, bs) -> Case(sub |-> exprs, sub |-> bs)

fun (|->)(sub: list<(tName, expr)>, Branch(patts, guards): branch): pure branch
  val bvpat = patts.map(boundVars).unions
  val sub' = sub.filter(fn((nm, _)) !bvpat.member(nm))
  Branch(patts, sub' |-> guards)

fun (|->)(sub: list<(tName, expr)>, Guard(test, expr): guard): pure guard
  Guard(sub |-> test, sub |-> expr)

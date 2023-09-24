import compiler/core/core
import newstd/data/linearset
import compiler/common/name
import compiler/type/typevar

fun isTopLevel(d: def)
  val freeVar = d.defExpr.freeVars.list.map(fn(TName(nm)) nm).filter(fn(nm) !nm.isQualified && d.defName.unqualify != nm)
  val freeTv = d.defExpr.freeTypeVars
  freeVar.is-nil && freeTv.is-empty

fun freeLocals(e: expr)
  e.freeVars.filter(fn(TName(nm)) !nm.isQualified)

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
    Cons(dg, dgs) -> dg.freeVars + (freeVars(dgs, e) - dg.boundVars)

fun freeVars(defg: defGroup): pure linearSet<tName>
  defg.flatten.map(freeVars).unions

fun boundVars(defg: defGroup): pure linearSet<tName>
  defg.flatten.map(boundVars).unions

fun boundVars(Def(nm, tp): def): pure linearSet<tName>
  tnamesEmpty + TName(nm, tp)

fun freeVars(Def(_, _, e): def): pure linearSet<tName>
  e.freeVars
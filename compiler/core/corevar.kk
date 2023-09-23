import compiler/core/core
import newstd/data/linearset
import compiler/common/name
import compiler/type/typevar

fun isTopLevel(d: def)
  val freeVar = d.expr.freeVars.list.map(fn(TName(nm)) nm).filter(fn(nm) !nm.isQualified && d.name.unqualify != nm)
  val freeTv = d.expr.freeTypeVars
  freeVar.is-nil && freeTv.is-empty

fun freeLocals(expr: expr)
  expr.freeVars.filter(fn(TName(nm)) !nm.isQualified)

fun freeVars(l: list<expr>): pure linearSet<tName>
  l.map(freeVars).unions

fun freeVars(expr: expr): pure linearSet<tName>
  match expr
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

fun freeVars(defGroups: defGroups, expr: expr): pure linearSet<tName>
  match defGroups
    [] -> expr.freeVars
    Cons(dg, dgs) -> dg.freeVars + (freeVars(dgs, expr) - dg.boundVars)

fun freeVars(defg: defGroup): pure linearSet<tName>
  defg.flatten.map(freeVars).unions

fun boundVars(defg: defGroup): pure linearSet<tName>
  defg.flatten.map(boundVars).unions

fun boundVars(Def(name, tp): def): pure linearSet<tName>
  tnamesEmpty + TName(name, tp)

fun freeVars(Def(_, _, expr): def): pure linearSet<tName>
  expr.freeVars
import compiler/core/core

fun isTopLevel(Def(name, tp, expr, vis, isVal, inl, range, doc))
  val freeVar = expr.freeVars.tnamesList.map(name).filter(fn(nm) !nm.isQualified && name.unqualify != nm)
  val freeTv = expr.freeTypeVars
  freeVar.is-nil && freeTypeVars.is-empty

fun freeLocals(expr: expr)
  expr.freeVars.filter(fn(TName(nm)) !nm.isQualified)


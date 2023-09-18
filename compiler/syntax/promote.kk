import compiler/common/name
import compiler/common/range
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/syntax/syntax
import newstd/data/linearset

fun promoteType(tp: userType): div userType
  val free = tp.freeTypeVars
  if free.is-empty then tp
  else
    val (someVars, forallVars) = free.list.partition(fn(x) x.isSomeVar)
    quantify(QSome, someVars.map(toTypeBinder), quantify(QForall, forallVars.map(toTypeBinder), tp))

fun promoteFree(bound: list<userTypeBinder>, tps: list<userType>): div list<userTypeBinder>
  (tps.freeTypeVars(freeTypeVars) - (namesEmpty + bound.map(name))).list.map(toTypeBinder)









fun isSomeVar(n: name)
  n.isWildcard




fun quantify(q: userQuantifier, tbinders: list<userTypeBinder>, tp: userType): userType
  tbinders.foldr(tp, fn(tb, t) TpQuan(q, tb, t, Range(tb.range.start, t.range.end)))





fun toTypeBinder(n: name): userTypeBinder
  TypeBinder(n, KindNone, rangeNull, rangeNull)
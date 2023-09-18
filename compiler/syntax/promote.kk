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


fun promote(somePars:list<userTypeBinder>, forallPars: list<userTypeBinder>, preds: list<userType>, mbResTp: maybe<(maybe<userType>, userType)>, expr: userExpr): div userExpr
// TODO: Do this
  promote(somePars, forallPars, preds, mbResTp, expr)

fun isSomeVar(n: name)
  n.isWildcard


fun qualify(tp: userType, preds: list<userType>): userType
  TpQual(preds, tp)

fun quantify(q: userQuantifier, tbinders: list<userTypeBinder>, tp: userType): userType
  tbinders.foldr(tp, fn(tb, t) TpQuan(q, tb, t, Range(tb.range.start, t.range.end)))

fun toTypeBinder(n: name): userTypeBinder
  TypeBinder(n, KindNone, rangeNull, rangeNull)

fun promoteTpVars(x: (name, either<userType, range>), vars: nameSet): div (name, either<userType, range>)
  match x.snd
    Right(_) -> x
    Left(u) -> (x.fst, Left(u.promoteTpVars(vars)))

fun promoteTpVars(tp: userType, vars: nameSet): div userType
  match tp
    TpQuan(quant, tb, t, rng) -> TpQuan(quant, tb, t.promoteTpVars(vars - tb.name), rng)
    TpQual(preds, t) -> TpQual(preds.map(fn(p) p.promoteTpVars(vars)), t.promoteTpVars(vars))
    TpFun(args, eff, t, rng) -> TpFun(args.map(fn((name, t1)) (name, t1.promoteTpVars(vars))), eff.promoteTpVars(vars), t.promoteTpVars(vars), rng)
    TpApp(t, args, rng) -> TpApp(t.promoteTpVars(vars), args.map(fn(t') t'.promoteTpVars(vars)), rng)
    TpVar(name, rng) -> TpVar(name, rng)
    TpCon(name, rng) -> if vars.member(name) then TpVar(name, rng) else TpCon(name, rng)
    TpParens(t, rng) -> TpParens(t.promoteTpVars(vars), rng)
    TpAnn(t, k) -> TpAnn(t.promoteTpVars(vars), k)

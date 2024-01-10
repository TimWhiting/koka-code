import compiler/common/name
import compiler/common/range
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/syntax/syntax
import newstd/data/linearset

fun promoteType(tp: userType): div userType
  val free = tp.free-type-vars
  if free.is-empty then tp
  else
    val (someVars, forallVars) = free.list.partition(fn(x) x.isSomeVar)
    quantify(QSome, someVars.map(toTypeBinder), quantify(QForall, forallVars.map(toTypeBinder), tp))

fun promoteFree(bound: list<userTypeBinder>, tps: list<userType>): div list<userTypeBinder>
  (tps.free-type-vars(free-type-vars) - (namesEmpty + bound.map(name))).list.map(toTypeBinder)

fun promote(somePars:list<userTypeBinder>, forallPars: list<userTypeBinder>, preds: list<userType>, mbResTp: maybe<(maybe<userType>, userType)>, uexpr: userExpr): pure userExpr
  fun resType(expr': userExpr)
    match expr'
      Parens(e, n, r) -> 
        val (es, e') = e.resType
        (es, Parens(e', n, r))
      _ -> match mbResTp
        Just((mbteff, tres)) -> 
          ([
            (nameNil, match mbteff {Nothing -> Right(expr'.range); Just(teff) -> Left(teff)}),
            (nameNil, Left(tres))], expr')
  fun argresTypes(expr': userExpr)
    match expr'
      Parens(e, n, r) -> 
        val (es, e') = argresTypes(e)
        (es, Parens(e', n, r))
      Ann(e, t, r) -> 
        val (es, e') = argresTypes(e)
        (es, Ann(e', t, r))
      Lam(args, e, r) ->
        val (es, e1) = e.resType
        val (fs, args') = args.map(fn(b)
          match b.binderType
            Nothing -> ((b.name, Right(r)), b)
            Just(t) ->
              val optTp = match b.expr
                Nothing -> t
                Just -> TpApp(TpCon(nameTpOptional, t.range), [t], t.range)
              ((b.name, Left(optTp)), b(binderType=Nothing))
        ).unzip
        (fs ++ es, Lam(args', e1, r))
      _ -> ([], expr')
  
  val (argresTps, expr') = argresTypes(uexpr)
  if argresTps.all(fn(a) a.snd.is-right) then uexpr
  else
    // promote quantified variables of TpCon to TpVar
    val quantified = namesEmpty + somePars.map(name) + forallPars.map(name)
    val argresTypes1 = argresTps.map(fn(a) promoteTpVars(a, quantified))
    // create full type by inserting some types if no parameter was annotated
    val (namess, argresTypes2) = list(1, argresTypes1.length).zip(argresTypes1).map(insertSome).unzip
    val Cons(resType', Cons(effType, rargsTypes)) = argresTypes2
    val names = namess.concat
    val eff = effType.snd
    val funTp = TpFun(rargsTypes.reverse, eff, resType'.snd, expr'.range)
    // Quantify over free type variables
    val implicit = (funTp.free-type-vars - (quantified + names)).list
    // Create fully quantified type
    val (impSome, impForall) = implicit.partition(isSomeVar)
    val fullTp =
      quantify(QSome, somePars ++ (names ++ impSome).map(toTypeBinder),
      quantify(QForall, forallPars ++ impForall.map(toTypeBinder), 
      qualify(funTp, preds)))
    Ann(expr', fullTp, expr'.range.combine(fullTp.range))

fun insertSome((i, (name, eitherTp)): (int, (name, either<userType, range>)))
  match eitherTp
    Left(t) -> ([], (name, t))
    Right(r) ->
      val tn = i.newImplicitTypeVarName
      ([tn], (name, TpVar(tn, r)))

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

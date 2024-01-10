import compiler/common/range
import compiler/common/name
import compiler/kind/kind
import compiler/type/type
import compiler/type/typevar
import compiler/core/core
import compiler/type/assumption
import compiler/common/syntax
import compiler/platform/config

pub infixr 5 (|->)
type evidence
  Ev(evName: tName, pred: pred, evRange: range)

fun (|->)(s: sub, e: evidence): pure evidence
  val newPred = typevar/(|->)(s, e.pred)
  e(pred=newPred)

fun (|->)(s: sub, l: list<evidence>): pure list<evidence>
  l.map(fn(e) s |-> e)

fun freeTypeVars(e: evidence)
  typevar/freeTypeVars(e.pred)

// fun boundTypeVars(e: evidence)
//   typevar/boundTypeVars(e.pred)

fun show(e: evidence)
  compiler/type/type/show(e.pred)

// instantiate a type
fun instantiate(tp: ktype, r: range)
  val (_, _, rho, _) = tp.instantiateNoEx(r)
  rho

// Instantiate a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun instantiateEx(tp: ktype, r: range)
  val (ids, preds, rho, coref) = tp.instantiateExFl(Meta, r)
  val (erho, coreg) = rho.extend
  (ids, preds, erho, fn(e) coreg(coref(e)))

// Instantiate a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun instantiateNoEx(tp: ktype, r: range)
  val (ids, preds, rho, coref) = tp.instantiateExFl(Meta, r)
  (ids, preds, rho, fn(e) coref(e))

//  Ensure the result of function always gets an extensible effect type
// This is necessary to do on instantiation since we simplify such effect variables
// away during generalization. Effectively, the set of accepted programs does not
// change but the types look simpler to the user.
fun extend(tp: ktype)
  match tp.expandSyn
    TFun(args, eff, res) ->
      val (ls, tl) = eff.extractOrderedEffect
      if tl.isEffectEmpty then
        val tv = freshTVar(kindEffect, Meta)
        val openEff = ls.effectExtends(tv)
        val openTp = TFun(args, openEff, res)
        (openTp, fn(c) openEffect(eff, openEff, tp, openTp, c))
      else
        (tp, id)
    _ -> (tp, id)

// Skolemize a type
fun skolemize(tp: ktype, r: range)
  val (_, _, rho, _) = tp.skolemizeEx(r)
  rho

// Skolemize a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun skolemizeEx(tp: ktype, r: range)
  tp.instantiateExFl(Skolem, r)

// General instantiation for skolemize and instantiate
fun instantiateExFl(tp: ktype, fl: flavour, r: range): <uniquePhase, comp-flags, pure> (list<typeVar>, list<evidence>, ktype, expr -> e expr)
  match tp.splitPredType
    ([], [], rho) -> ([], [], rho, id)
    (vars, preds, rho) ->
      val (tvars, sub) = freshSubX(TVar, fl, vars)
      val srho = sub |-> rho
      val spreds = preds.map(fn(p) sub |-> p)
      val pnames = spreds.map(predName)
      val corevars = pnames.map(fn(n) Var(n, InfoNone))
      val evidence = pnames.zip(spreds).map(fn((n, p)) Ev(n, p, r))
      (tvars, evidence, srho, if corevars.is-nil then id else id)

fun predName(p: pred)
  val name = match p
    PredSub -> freshName("sub")
    PredIFace(iname) -> freshName(iname.show)
  TName(name, p.predType)

fun freshSub(fl: flavour, vars: list<typeVar>)
  val tvars = vars.map(fn(tv) freshTypeVar(tv.kind, fl))
  val sub = vars.zip(tvars.map(TVar)).subNew
  (tvars, sub)

fun freshSubX(makeTVar: (typeVar -> ktype), fl: flavour, vars: list<typeVar>)
  val tvars = vars.map(fn(tv) freshTypeVar(tv.kind, fl))
  val sub = vars.zip(tvars.map(makeTVar)).subNew
  (tvars, sub)

fun freshSkolems(k: kind, n: int)
  freshTVars(k, Skolem, n)

fun freshTVars(k: kind, fl: flavour, n: int): uniquePhase list<ktype>
  list(1, n).map(fn(_) freshTVar(k, fl))

fun freshTVar(k: kind, fl: flavour): uniquePhase ktype
  TVar(freshTypeVar(k, fl))
  


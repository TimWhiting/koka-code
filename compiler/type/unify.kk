import compiler/lib/pprint
import compiler/common/range
import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/common/syntax
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/unify
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/type/pretty
import compiler/type/operations
import compiler/core/core
import newstd/data/linearset

effect unify
  final ctl unifyError(e: unifyErr): a
  fun extendSub(tv: typeVar, t: ktype): ()
  fun getSubst(): sub

fun withErr(e: unifyErr -> unifyErr, f: () -> <unify|e> a): <unify|e> a
  with override
    final ctl unifyError(er) unifyError(e(er))
    fun extendSub(tv, t) extendSub(tv, t)
    fun getSubst() getSubst() 
  f()

fun subst(x: ktype): <pure,unify> ktype
  getSubst() |-> x

type unifyErr
  NoMatch
  NoMatchKind
  NoMatchPred
  NoMatchSkolem(k: kind)
  NoMatchEffect(e1: ktype, e2: ktype)
  NoSubsume
  NoEntail
  Infinite
  NoArgMatch(i1: int, i2: int)

fun matchKinds(kinds1: list<kind>, kinds2: list<kind>): <div,unify> ()
  match (kinds1, kinds2)
    (Nil, Nil) -> ()
    (Cons(k1, k1s), Cons(k2, k2s)) -> 
      if matchKind(k1, k2) then 
        matchKinds(k1s, k2s)
      else
        unifyError(NoMatchKind)
    _ -> unifyError(NoMatchKind)

fun compareLabel(l1: ktype, l2: ktype)
  val name1 = l1.labelNameEx.fst
  val name2 = l2.labelNameEx.fst
  name1.labelNameCompare(name2)

fun unifyLabels(ls1: list<ktype>, ls2: list<ktype>, closed1: bool, closed2: bool): unify (list<ktype>, list<ktype>)
  match (ls1, ls2)
    (Nil, Nil) -> (Nil, Nil)
    (Cons, Nil) -> ([], [])
    (Nil, Cons) -> ([], [])
    (Cons(l1, ll1), Cons(l2, ll2)) ->
      val (name1, i1, args1) = l1.labelNameEx
      val (name2, i2, args2) = l2.labelNameEx
      match name1.labelNameCompare(name2)
        Lt -> 
          val (ds1, ds2) = unifyLabels(ll1, ls2, closed1, closed2)
          (ds1, Cons(l1, ds2))
        Gt ->
          val (ds1, ds2) = unifyLabels(ls1, ll2, closed1, closed2)
          (Cons(l2, ds1), ds2)
        Eq -> // labels are equal
          match (args1, args2)
            ([TVar(TypeVar(id1, kind1, sort1))], ([TVar (TypeVar(id2, kind2, sort2))]))
              | kind1 == kindScope && kind2 == kindScope && id1 != id2 && sort1.is-skolem && sort2.is-skolem ->
                if (id1 < id2) then
                  val (ds1, ds2) = unifyLabels(ll1, ls2, closed1, closed2)
                  (ds1, Cons(l1, ds2))
                else
                  val (ds1, ds2) = unifyLabels(ls1, ll2, closed1, closed2)
                  (Cons(l2, ds1), ds2)
            _ ->
              unify(l1, l2) // for heap effects and kind checks
              val ll1' = ll1.subst
              val ll2' = ll2.subst
              unifyLabels(ll1', ll2', closed1, closed2)

fun unifyEffectVar(tv1: typeVar, tp2: ktype): <pure,unify> ()
  val (ls2, tl2) = tp2.extractOrderedEffect // ls2 must be non-empty
  match tl2.expandSyn 
    // e ~ <div,exn|e> ~> e := <div,exn|e'>
    TVar(tv2) | tv1 == tv2 -> unifyError(Infinite)
    _ ->
      val tv = freshTVar(kindEffect, Meta)
      unifyTVar(tv1, effectExtends(ls2, tl2))

fun extractNormalizeEffect(tp: ktype): <pure,unify> (list<ktype>, ktype)
  val tp' = tp.subst
  tp'.extractOrderedEffect

// Unify effects
fun unifyEffect(tp1: ktype, tp2: ktype): unify ()
  val (ls1, tl1) = tp1.extractNormalizeEffect
  val (ls2, tl2) = tp2.extractNormalizeEffect
  val (ds1, ds2) = unifyLabels(ls1, ls2, tl1.isEFfectEmpty, tl2.isEFfectEmpty)
  match (tl1.expandSyn, tl2.expandSyn)
    (TVar(TypeVar(id1, kind1, Meta)), TVar(TypeVar(id2, kind2, Meta))) | id1 == id2 && !(ds1.is-empty && ds2.is-empty) -> 
      unifyError(Infinite)
    _ ->
      val tail1 = if ds1.is-empty then tl1 else
        val tv1 = freshTVar(kindEffect, Meta)
        unify(tl1, ds1.effectExtends(tv1))
        tv1
      val stl2 = tl2.subst
      val tail2 = if ds2.is-empty then stl2 else
        val tv2 = freshTVar(kindEffect, Meta)
        unify(stl2, ds2.effectExtends(tv2))
        tv2
      val stail1 = tail1.subst
      unify(stail1, tail2)
      tp1.subst
      tp2.subst
      ()

fun unifyPred(p1: pred, p2: pred): unify ()
  match (p1, p2)
    (PredSub(t1, t2), (PredSub(u1, u2))) ->
      unify(t1, u1)
      unify(t2.subst, u2.subst)
    (PredIFace(name1, ts1), PredIFace(name2, ts2)) | name1 == name2 ->
      unifies(ts1, ts2)
    _ -> unifyError(NoMatchPred)

// Unify predicates (applies a substitution before each unification)
fun unifyPreds(l1: list<pred>, l2: list<pred>): <pure,unify> ()
  match (l1, l2)
    (Nil, Nil) -> ()
    (Cons(p1, ps1), Cons(p2, ps2)) ->
      unifyPred(p1.subst, p2.subst)
      unifyPreds(ps1, ps2)
    _ -> throw("type/unify unifyPreds")

// Unify two equal length lists of types, and apply a substitution before each unification
fun unifies(l1: list<ktype>, l2: list<ktype>): <pure,unify> ()
  match (l1, l2)
    (Nil, Nil) -> ()
    (Cons(t1, ts1), Cons(t2, ts2)) ->
      unify(t1.subst, t2.subst)
      unifies(ts1, ts2)
    _ -> throw("type/unify unifies")

// Unify a type variable with a type
fun unifyTVar(tv: typeVar, tp: ktype): <pure,unify> ()
  match tv
    TypeVar(id, k, Meta) -> 
      val etp = tp.expandSyn
      if etp.freeTypeVars.fuv.list.any(fn(tv') tv == tv') then
        match etp
          TVar(tv') | tv == tv' -> () // i.e. a ~ id<a>
          _ -> unifyError(Infinite)
      else
        match etp
          TVar(TypeVar(_, _, Bound)) -> unifyError(NoMatch) // can't unify with bound variables
          TVar(tv2 as TypeVar(id2, _, Meta)) | id <= id2 ->
            if id < id2 then unifyTVar(tv2, TVar(tv)) else () // TODO: Kind Check?
          _ ->
            if !matchKind(k, tp.kind) then
              trace("unifyTVar: kinds: typevar var:\n" ++ k.show ++ "\nand:\n" ++ tp.kind.show ++ "\ntype:\n" ++ tp.show)
              unifyError(NoMatchKind)
            else
              extendSub(tv, tp)
    _ -> throw("type/unify unifyTVar: valued with skolem or bound variable")

// Unify two types
fun unify(t1: ktype, t2: ktype): <pure,unify> ()
  match (t1, t2)
    // effects
    (TApp(TCon(tc1)), TApp(TCon(tc2))) | tc2 == tconEffectExtend && tc1 == tconEffectExtend ->
      unifyEffect(t1, t2)
    (TApp(TCon(tc1)), TVar(tv2)) | tc1 == tconEffectExtend && tv2.is-meta ->
      unifyEffectVar(tv2, t2)
    (TVar(tv1), TApp(TCon(tc2))) | tc2 == tconEffectExtend && tv1.is-meta ->
      unifyEffectVar(tv1, t1)
    // type variables
    (TVar(v1), TVar(v2)) | v1 == v2 -> () // TODO: Kind check?
    (TVar(tv as TypeVar(_, _, Meta)), _) -> unifyTVar(tv, t2)
    (_, TVar(tv as TypeVar(_, _, Meta))) -> unifyTVar(tv, t1)
    // constants
    (TCon(tc1), TCon(tc2)) | tc1 == tc2 -> ()
    // type applications
    (TApp(t1, ts1), TApp(u1, us2)) ->
      val len1 = ts1.length
      val len2 = us2.length
      if len1 == len2 then 
        unify(t1, u1)
        unifies(ts1, us2)
      elif len1 < len2 then
        unify(t1, TApp(u1, us2.take(len2 - len1)))
        unifies(ts1, us2.drop(len2 - len1))
      else
        unify(TApp(t1, ts1.take(len1 - len2)), u1)
        unifies(ts1.drop(len1 - len2), us2)
    // functions
    (TFun(args1, eff1, res1), TFun(args2, eff2, res2)) | args1.length == args2.length ->
      unifies(res1 ++ args1.map(snd), res2 ++ args2.map(snd))
      fun effErr(e: unifyErr)
        match e
          NoMatch -> NoMatchEffect(eff1, eff2)
          NoMatchEffect -> NoMatchEffect(eff1, eff2)
          _ -> e
      with withError(effErr)
      unify(eff1, eff2)
    // quantified types
    (TForall(vars1, preds1, tp1), (TForall(vars2, preds2, tp2))) | vars1.length == vars2.length && preds1.length == preds2.length ->
      // match kidns of quanitifers
      matchKinds(vars1.map(getKind), vars2.map(getKind))
      // replace with shared bound variables in both types
      // note: assumes ordered quantifiers and ordered predicates
      // note: we don't use Skolem as a Meta variable can unify with a Skolem but not with a Bound one
      val vars = kinds.map(fn(k) freshTVar(k, Bound))
      val sub1 = vars1.zip(vars).subNew
      val sub2 = vars2.zip(vars).subNew
      val stp1 = sub1 |-> tp1
      val stp2 = sub2 |-> tp2
      val spreds1 = sub1 |-> preds1
      val spreds2 = sub2 |-> preds2
      // and unify the results
      unify(stp1, stp2)
      unifyPreds(spreds1, spreds2)
      // No need to check for escaping skolems as we don't unify to bound variables
    // Special unsafe(!) handling of continuations; just for cps translation :-( 
    (TSyn(syn1, args1, tp1), TSyn(syn2, args2, tp2)) | syn1.name == nameTpCont && syn2.name == nameTpCont ->
      val n = args1.length
      unify(args1.take(n - 1), args2.take(n - 1))
    (TSyn(syn1, args1, tp1), TFun([(_, tpar)], teff, tres)) | syn1.name == nameTpCont ->
      unifies(args1.take(2), [tpar, teff])
    // synonyms
    (TSyn(syn1, args1, tp1), TSyn(syn2, args2, tp2)) ->
      if syn1.rank > syn2.rank then unify(tp1, t2) else unify(t1, tp2)
    (TSyn(_, _, tp1), tp2) -> unify(tp1, tp2)
    (tp1, TSyn(_, _, tp2)) -> unify(tp1, tp2)
    // No match
    (TVar(TypeVar(_, kind, Skolem)), TVar(TypeVar(_, _, Skolem))) ->
      unifyError(NoMatchSkolem(kind))
    _ -> unifyError(NoMatch)

/// entails(skolems, known, preds) 
/// 
/// Returns both predicates that need to be proved and a core transformer 
///  that applies the evidence for `preds` and abstracts for those in `known`. 
/// The `preds` are entailed by `known` and predicates containing a type variable in `skolems` must
/// be entailed completely by other predicates (not containing such skolems).
fun entails(skolems: tvs, known: list<evidence>, evs: list<evidence>): unify (list<evidence>, expr -> e expr)
  match evs
    Nil -> (Nil, id)
    evs | unsafe-total({known.map(pred) == evs.map(pred)}) -> (Nil, id) // TODO: should construct evidence from known to preds (simple one-to-one name mapping)
    Cons(ev, evs) ->
      match ev.pred
        PredIFace(name, [_, _, _]) | name == namePredHeapDiv -> // can always be solved
          entails(skolems, known, evs)
        _ -> unifyError(NoEntail)

// Subsumption
// subsume(free, t1, t2) holds if `t2` can be instantiated to `t1` where
// `free` are the free type variables in the assumption.
// Returns under which predicates this holds and a core transformer that needs to be
// applied to the expression of type `t2`. Also returns a new type for the expected type `tp1` where 'some'
// types have been properly substituted (and may be quantified).
fun subsume(rng: range, free: tvs, tp1: ktype, tp2: ktype): unify (ktype, list<evidence>, expr -> e expr)
  // skolemize, instantiate and unify
  val (sks, evs1, rho1, core1) = skolemizeEx(rng, tp1)
  val (tvs, evs2, rho2, core2) = skolemizeEx(rng, tp2)
  unify(rho2, rho1)
  // escape check: no skolems should escape into the environment
  // entailment check: predicates should be entailed
  // TODO: we should check for skolems since predicates with skolems must be entailed directly
  val sub = getSubst()
  val allfree = free ++ tp1.freeTypeVars
  val escaped = sub.list.filter(fn((tv, tp)) allfree.any(fn(t) t == tv)).map(snd).freeTypeVars.fsv // TODO: 
  if escaped.disjoint(sks.tvsNew) then ()
  else unifyError(NoSubsume)
  val (evsEnt, coreEnt) = entails(sks.tvsNew, sub |-> evs1, sub |-> evs2)
  // final type
  val (vars, ssub) = freshSub(Bound, sks)
  val subx = ssub |-> sub
  val tp = quantifyType(vars, qualifyType(evs1.map(fn(ev) subx |-> ev.pred)), subx |-> rho1) // TODO: do rho1 and we get skolem errors: see Prelude.choose
  // return
  (tp, subx |-> evsEnt, 
    fn(expr) addTypeLambdas(vars, // generalize 
      subx |-> coreEnt( // apply evidence evs2 & abstract evidence evs1
        addTypeApps(tvs, expr)))) // instantiate

/// Does a function type match the given arguments? if the first argument 'matchSome' is ture,
/// it is considered a match even if not all arguments to the function are supplied
fun matchArguments(matchSome: bool, rng: range, free: tvs, tp: ktype, fixed: list<ktype>, namedArgs: list<(name,ktype)>): unify ()
  val rho1 = instantiate(rng, tp)
  match rho1.splitFunType
    Nothing -> unifyError(NoMatch)
    Just((pars, _, _)) ->
      if fixed.length + namedArgs.length > pars.length then unifyError(NoMatch)
      else // subsume fixed parameters
        val (fpars, npars) = pars.split-at(fixed.length)
        fpars.map(snd).zip(fixed).map(fn((tpars, targ)) subsume(rng, free, tpar.unOptional, targ))
        // subsume named parameters
        namedArgs.map fn((name, targ))
          match npars.lookup(fn(n) n == name)
            Nothing -> unifyError(NoMatch)
            Just(tpar) -> subsume(rng, free, tpar, targ.makeOptional)
        // check the rest is optional
        val rest = npars.filter(fn((nm, tpar)) !(namedArgs.map(fst).any(fn(n) n == nm)))
        if matchSome || rest.all(is-optional) then ()
        else unifyError(NoMatch)

/// Does a type have the given named arguments?
fun matchNamed(rng: range, tp: ktype, n: int, namedArgs: list<name>): unify ()
  val rho1 = instantiate(tp, rng)
  match rho1.splitFunType
    Nothing -> unifyError(NoMatch)
    Just((pars, _, _)) ->
      if n + namedArgs.length > pars.length then unifyError(NoMatch)
      else
        val npars = pars.drop(n)
        val names = npars.map(fst)
        if namedArgs.all(fn(n) names.any(fn(n') n == n')) then 
          val rest = npars.filter(fn((nm, tp)) !(namedArgs.any(fn(n) n == nm))).map(snd)
          if res.all(fn(tp) tp.isOptional) then ()
          else unifyError(NoMatch)
        else unifyError(NoMatch)

/// Do two types overlap on the argument types? Used to check for overlapping definitions of overloaded identifiers.
fun overlaps(rng: range, free: tvs, tp1: ktype, tp2: ktype): unify ()
  val rho1 = instantiate(tp1, rng)
  val rho2 = instantiate(tp2, rng)
  match (rho1.splitFunType, rho2.splitFunType)
    // Values always overlap
    (Nothing, _) -> ()
    (_, Nothing) -> ()
    // rest
    (Just((targs1, _, _)), Just((targs2, _, _))) ->
      val (fixed1, optional1) = targs.map(snd).span(fn(tp) !tp.is-optional)
      val (fixed2, optional2) = targs.map(snd).span(fn(tp) !tp.is-optional)
      val hi = max(fixed1.length, fixed2.length)
      val fo1 = (fixed1 ++ optional1.map(unOptional)).take(hi)
      val fo2 = (fixed2 ++ optional2.map(unOptional)).take(hi)
      if fo1.length != fo2.length then unifyError(NoMatch) // one has more fixed arguments than the other can ever get
      else
        unifies(fo1, fo2)
        ()
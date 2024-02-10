import compiler/type/type
import newstd/data/linearset
import newstd/data/linearmap
import compiler/core/core
import compiler/type/kind
import compiler/kind/kind
import compiler/common/syntax
import compiler/common/name

pub infixr 5 (|->)

alias tvs = linearSet<typeVar>
alias sub = linearMap<typeVar, ktype>

val emptyTvs = linearSet([])

val emptySub = linearMap([])

fun fuv(tvs: tvs): linearSet<typeVar>
  tvs.filter(fn(tv) tv.flavour.is-meta)
fun fsv(tvs: tvs): linearSet<typeVar>
  tvs.filter(fn(tv) tv.flavour.is-skolem)
fun fbv(tvs: tvs): linearSet<typeVar>
  tvs.filter(fn(tv) tv.flavour.is-bound)

fun subNew(l: list<(typeVar, ktype)>): exn sub
  if l.all(fn((tv, t)) tv.kind == t.kind) then
    linearMap(l)
  else
    throw("type/typevar: subNew kind mismatch")

fun subDom(s: sub): tvs
  tvsNew(s.list.map(fst))

fun subRange(s: sub): list<ktype>
  s.list.map(snd)

fun subList(s: sub): list<(typeVar, ktype)>
  s.list

fun subCommon(s1: sub, s2: sub): list<(typeVar, (tau, tau))>
  s1.list.map(fn(s) s2.maybeGet(s.fst).map(fn(t) (s.fst, (s.snd, t)))).concat-maybe

fun subSingle(tvar: typeVar, tau: tau)
  // Top assertion is invalid; it can happen (and happens) in the CoreF typechecker when
  // typechecking (forall a. f a) with f :: forall b. b -> b, that a bound variable (b) with
  // number ID must be substituted for another bound variable (a), which *could* have the same
  // ID. If we want to avoid this, we must ensure that all IDs are distinct; in particular,
  // the IDs of built-in types such as .select must be distinct from further IDs generated
  // by the compiler.
  if tau.free-type-vars.member(tvar) then
    throw("type/typevar: subSingle: recursive type " ++ tvar.show)
  if tau.kind != tvar.kind then
    throw("type/typevar: subSingle: kind mismatch " ++ tau.show ++ " " ++ tvar.show)
  linearMap([(tvar, tau)])

fun subLookup(s: sub, tv: typeVar): maybe<tau>
  s.maybeGet(tv)

fun subRemove(s: sub, tvars: list<typeVar>): sub
  s.removeAll(tvars)

fun subFind(s: sub, tv: typeVar): exn tau
  s.get(tv)

fun subCompose(s1: sub, s2: sub): pure sub
  s1.union(s1 |-> s2)

fun single(tv: typeVar) 
  linearSet([tv])

fun tvsNew(tv: list<typeVar>) 
  linearSet(tv)

fun free-type-vars(ps: list<a>, ?free-type-vars: (a) -> pure tvs): pure tvs
  ps.map(f).unions

fun free-type-vars(pred: pred): pure tvs
  match pred
    PredSub(sub, super) -> sub.free-type-vars + super.free-type-vars
    PredIFace(_, args) -> args.map(free-type-vars).unions

fun free-type-vars(tp: ktype): pure tvs
  match tp
    TForAll(vars, preds, t) -> 
      val tv1 :tvs = t.free-type-vars + preds.free-type-vars
      tv1 - vars
    TFun(args, eff, res) -> 
      val tv1: tvs = args.map(fn(a) a.snd.free-type-vars).unions 
      val tv2: tvs = tv1 + res.free-type-vars
      tv2 + eff.free-type-vars
    TCon -> emptyTvs
    TVar(tv) -> single(tv)
    TApp(t, args) -> t.free-type-vars + args.map(fn(a) a.free-type-vars).unions
    TSyn(_, xs, t) -> t.free-type-vars + xs.map(free-type-vars).unions

fun free-type-vars(e0: expr): pure tvs
  match e0
    Lam(tn, eff, e) -> 
      val tv1: tvs = tn.free-type-vars + eff.free-type-vars
      tv1 + e.free-type-vars
    Var(tn) -> tn.free-type-vars
    App(a, b) -> a.free-type-vars + b.free-type-vars
    TypeLam(tvs, e) -> e.free-type-vars - tvs
    TypeApp(e, tp) -> e.free-type-vars + tp.free-type-vars
    Con(tn) -> tn.free-type-vars
    ELit -> emptyTvs
    Let(defGroups, e) -> defGroups.map(free-type-vars).unions + e.free-type-vars
    Case(es, bs) -> es.free-type-vars + bs.map(free-type-vars).unions

fun free-type-vars(dg: defGroup): pure tvs
  match dg
    DefRec(defs) -> defs.map(free-type-vars).unions
    DefNonRec(e) -> free-type-vars(e)

fun free-type-vars(d: def): pure tvs
  d.ktype.free-type-vars + d.defExpr.free-type-vars

fun free-type-vars(bs: branch): pure tvs
  match bs
    Branch(p, e) -> 
      val tv1: tvs = e.free-type-vars - p.boundTypeVars
      tv1 + p.free-type-vars

fun free-type-vars(p: pattern): pure tvs
  match p
    PatVar(tn, pat) -> tn.free-type-vars + pat.free-type-vars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1:tvs = tn.free-type-vars + args.free-type-vars
      val tv2:tvs = tv1 + targs.free-type-vars 
      val tv3:tvs = tv2 + tres.free-type-vars
      tv3 - exists0
    PatWild -> emptyTvs
    PatLit(_) -> emptyTvs

fun free-type-vars(gd: guard): pure tvs
  match gd
    Guard(e, e2) -> e.free-type-vars + e2.free-type-vars

fun free-type-vars(TName(_, tp): tName): pure tvs
  tp.free-type-vars

fun boundTypeVars(l: list<a>, ?boundTypeVars: (a) -> pure tvs): pure tvs
  l.map(f).unions

fun boundTypeVars(p: pattern): pure tvs
  match p
    PatVar(tn, pat) -> tn.boundTypeVars + pat.boundTypeVars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1: tvs = tn.boundTypeVars + args.boundTypeVars
      val tv2: tvs = tv1 + targs.boundTypeVars
      val tv3: tvs = tv2 + tres.boundTypeVars
      tv3 + exists0.tvsNew
    PatWild -> emptyTvs
    PatLit(_) -> emptyTvs

fun boundTypeVars(tp: ktype): pure tvs
  match tp
    TForAll(vars, preds, t) -> 
      val tv1: tvs = preds.free-type-vars + t.boundTypeVars
      tv1 + vars
    TFun(args, eff, res) -> 
      val tv1: tvs = args.map(snd).boundTypeVars + res.boundTypeVars 
      tv1 + eff.boundTypeVars
    TSyn(_, _, t) -> t.boundTypeVars
    TApp(t, arg) -> t.boundTypeVars + arg.boundTypeVars
    _ -> emptyTvs

fun boundTypeVars(TName(_, tp): tName): pure tvs
  tp.boundTypeVars

fun (|->)(s1: sub, s2: sub): pure sub
  s2.map(fn(k, v) (k, s1 |-> v))

fun (|->)(s: sub, l: list<a>, ?(|->): (sub, a) -> e a): e list<a>
  l.map(fn(a) f(s, a))

fun (|->)(s: sub, tp: ktype): pure tau
  match tp
    TForAll(vars, preds, t) ->
      val sub' = s.subRemove(vars)
      TForAll(vars, preds.map(fn(p:pred) (|->)(sub', p)), sub' |-> t)
    TFun(args, eff, res) -> TFun(args.map(fn(a) (a.fst, s |-> a.snd)), s |-> eff, s |-> res)
    TCon -> tp
    TVar(tv) -> s.subFind(tv)
    TApp(t, args) -> TApp(s |-> t, args.map(fn(t') s |-> t'))
    TSyn(syn, xs, t) -> TSyn(syn, xs, s |-> t)

fun (|->)(s: sub, pred: pred): pure pred
  match pred
    PredSub(sub, super) -> PredSub(s |-> sub, s |-> super)
    PredIFace(iface, args) -> PredIFace(iface, args.map(fn(t) s |-> t))

fun (|->)(s: sub, tn: tName): pure tName
  match tn
    TName(n, tp) -> TName(n, s |-> tp)

fun (|->)(s: sub, p: pattern): pure pattern
  match p
    PatVar(tn, pat) -> PatVar(s |-> tn, s |-> pat)
    PatCon(tn, args, repr, targs, exists0, tres,  conInfo, skip) ->
      val sub' = s.subRemove(exists0)
      PatCon(s |-> tn, sub' |-> args, repr, sub' |-> targs, exists0, sub' |-> tres, conInfo, skip)
    PatWild -> PatWild
    PatLit(l) -> PatLit(l)

fun (|->)(s: sub, e: expr): pure expr
  match e
    Lam(tn, eff, e) -> Lam(s |-> tn, s |-> eff, s |-> e)
    Var(tn, x) -> Var(s |-> tn, x)
    App(a, b) -> App(s |-> a, s |-> b)
    TypeLam(tvs, e) -> 
      val sub' = s.subRemove(tvs)
      TypeLam(tvs, sub' |-> e)
    TypeApp(e, tp) -> TypeApp(s |-> e, s |-> tp)
    Con(tn, repr) -> Con(s |-> tn, repr)
    ELit(l) -> ELit(l)
    Let(defGroups, e) -> Let(defGroups.map(fn(dg) s |-> dg), s |-> e)
    Case(es, bs) -> Case(s |-> es, bs.map(fn(b) s |-> b))

fun (|->)(s: sub, dg: defGroup): pure defGroup
  match dg
    DefRec(defs) -> DefRec(defs.map(fn(d) s |-> d))
    DefNonRec(e) -> DefNonRec(s |-> e)

fun (|->)(s: sub, Def(name, scheme, expr, vis, isVal, inl, nameRng, doc): def): pure def
  Def(name, s |-> scheme, s |-> expr, vis, isVal, inl, nameRng, doc)

fun (|->)(s: sub, Branch(p, e): branch): pure branch
  val sub' = s.subRemove(p.boundTypeVars.list)
  Branch(s |-> p, sub' |-> e)

fun (|->)(s: sub, g: guard): pure guard
  match g
    Guard(e, e2) -> Guard(s |-> e, s |-> e2)

// TODO: More
fun freshTypeVar(k: kind, fl: flavour)
  val idbase = match fl
    Meta -> "_v"
    Skolem -> "$v"
    Bound -> "v"
  val id = uniqueId(idbase)
  TypeVar(id, k, fl)

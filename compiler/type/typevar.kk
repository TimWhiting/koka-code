import compiler/type/type
import compiler/core/core
import compiler/type/kind
import compiler/kind/kind
import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import std/data/linearset
import std/data/linearmap
import std/core/undiv

pub infixr 5 (|->)

alias tvs = linearSet<typeVar>
alias sub = linearMap<typeVar, ktype>

val tvs/empty:tvs = LinearSet([])

val sub/empty:sub = LinearMap([])

fun fuv(tvs: tvs): linearSet<typeVar>
  tvs.filter(fn(tv) tv.flavour.is-meta)
fun fsv(tvs: tvs): linearSet<typeVar>
  tvs.filter(fn(tv) tv.flavour.is-skolem)
fun fbv(tvs: tvs): linearSet<typeVar>
  tvs.filter(fn(tv) tv.flavour.is-bound)

fun new/sub(l: list<(typeVar, ktype)>): exn sub
  if l.all(fn((tv, t)) tv.kind == t.kind) then
    empty + l
  else
    throw("type/typevar: subNew kind mismatch")

fun sub/dom(s: sub): tvs
  tvs/empty + s.list.map(fst)

fun range(s: sub): list<ktype>
  s.list.map(snd)

fun common(s1: sub, s2: sub): list<(typeVar, (tau, tau))>
  s1.list.map(fn(s) s2.lookup(s.fst).map(fn(t) (s.fst, (s.snd, t)))).concat-maybe

fun sub/single(tvar: typeVar, tau: tau)
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
  LinearMap([(tvar, tau)])

fun sub/remove(s: sub, tvars: list<typeVar>): sub
  s.remove-all(tvars)

fun subtvs/remove(s: sub, tvars: tvs): sub
  s.remove-all(tvars.list)

fun find(s: sub, tv: typeVar): exn tau
  s.get(tv)

fun compose(s1: sub, s2: sub): pure sub
  s1.union(s1 |-> s2)

fun tv/single(tv: typeVar) 
  [tv]

fun new/tvs(tv: list<typeVar>) 
  tv

fun list/free-type-vars(ps: list<a>, ?free-type-vars: (a) -> div tvs): div tvs
  ps.map(free-type-vars).unions

fun pred/free-type-vars(pred: pred): div tvs
  match pred
    PredSub(sub, super) -> sub.free-type-vars + super.free-type-vars
    PredIFace(_, args) -> args.map(free-type-vars).unions

fun ktype/free-type-vars(tp: ktype): div tvs
  match tp
    TForAll(vars, preds, t) -> 
      val tv1 :tvs = t.free-type-vars + preds.free-type-vars
      tv1 - vars
    TFun(args, eff, res) -> 
      val tv1: tvs = args.map(fn(a) a.snd.free-type-vars).unions 
      val tv2: tvs = tv1 + res.free-type-vars
      tv2 + eff.free-type-vars
    TCon -> tvs/empty
    TVar(tv) -> LinearSet([tv])
    TApp(t, args) -> t.free-type-vars + args.map(fn(a) a.free-type-vars).unions
    TSyn(_, xs, t) -> t.free-type-vars + xs.map(free-type-vars).unions

fun exp/free-type-vars(e0: expr): div tvs
  match e0
    Lam(tn, eff, e) -> 
      val tv1: tvs = tn.free-type-vars + eff.free-type-vars
      tv1 + e.free-type-vars
    Var(tn) -> tn.free-type-vars
    App(a, b) -> a.free-type-vars + b.free-type-vars
    TypeLam(tvs, e) -> e.free-type-vars - tvs
    TypeApp(e, tp) -> e.free-type-vars + tp.free-type-vars
    Con(tn) -> tn.free-type-vars
    ELit -> tvs/empty
    Let(defGroups, e) -> defGroups.map(free-type-vars).unions + e.free-type-vars
    Case(es, bs) -> es.free-type-vars + bs.map(free-type-vars).unions

fun dg/free-type-vars(dg: defGroup): div tvs
  match dg
    DefRec(defs) -> defs.map(free-type-vars).unions
    DefNonRec(e) -> free-type-vars(e)

fun def/free-type-vars(d: def): div tvs
  d.ktype.free-type-vars + d.defExpr.free-type-vars

fun branch/free-type-vars(bs: branch): div tvs
  match bs
    Branch(p, e) -> 
      e.free-type-vars - p.boundTypeVars + p.free-type-vars

fun pat/free-type-vars(p: pattern): div tvs
  match p
    PatVar(tn, pat) -> tn.free-type-vars + pat.free-type-vars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1:tvs = tn.free-type-vars + args.free-type-vars
      val tv2:tvs = tv1 + targs.free-type-vars 
      val tv3:tvs = tv2 + tres.free-type-vars
      tv3 - exists0
    PatWild -> tvs/empty
    PatLit(_) -> tvs/empty

fun guard/free-type-vars(gd: guard): div tvs
  match gd
    Guard(e, e2) -> e.free-type-vars + e2.free-type-vars

fun tn/free-type-vars(TName(_, tp): tName): div tvs
  tp.free-type-vars

fun list/boundTypeVars(l: list<a>, ?boundTypeVars: (a) -> div tvs): div tvs
  l.map(boundTypeVars).unions

fun pat/boundTypeVars(p: pattern): div tvs
  match p
    PatVar(tn, pat) -> tn.boundTypeVars + pat.boundTypeVars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1: tvs = tn.boundTypeVars + args.boundTypeVars
      val tv2: tvs = tv1 + targs.boundTypeVars
      val tv3: tvs = tv2 + tres.boundTypeVars
      tv3 + exists0.tvs
    PatWild -> tvs/empty
    PatLit(_) -> tvs/empty

fun ktype/boundTypeVars(tp: ktype): div tvs
  match tp
    TForAll(vars, preds, t) -> 
      val tv1: tvs = preds.free-type-vars + t.boundTypeVars
      tv1 + vars
    TFun(args, eff, res) -> 
      val tv1: tvs = args.map(tuple2/snd).boundTypeVars + res.boundTypeVars 
      tv1 + eff.boundTypeVars
    TSyn(_, _, t) -> t.boundTypeVars
    TApp(t, arg) -> t.boundTypeVars + arg.boundTypeVars
    _ -> tvs/empty

fun tn/boundTypeVars(TName(_, tp): tName): div tvs
  tp.boundTypeVars

fun sub/(|->)(s1: sub, s2: sub): pure sub
  s2.map(fn(k, v) (k, s1 |-> v))

fun sublist/(|->)(s: sub, l: list<a>, ?(|->): (sub, a) -> e a): e list<a>
  l.map(fn(a) s |-> a)

fun ktype/(|->)(s: sub, tp: ktype): pure tau
  match tp
    TForAll(vars, preds, t) ->
      val sub' = s.remove(vars)
      TForAll(vars, preds.map(fn(p:pred) sub' |-> p), sub' |-> t)
    TFun(args, eff, res) -> TFun(args.map(fn(a) (a.fst, s |-> a.snd)), s |-> eff, s |-> res)
    TCon -> tp
    TVar(tv) -> s.find(tv)
    TApp(t, args) -> TApp(s |-> t, args.map(fn(t') s |-> t'))
    TSyn(syn, xs, t) -> TSyn(syn, xs, s |-> t)

fun pred/(|->)(s: sub, pred: pred): pure pred
  match pred
    PredSub(sub, super) -> PredSub(s |-> sub, s |-> super)
    PredIFace(iface, args) -> PredIFace(iface, args.map(fn(t) s |-> t))

fun tn/(|->)(s: sub, tn: tName): pure tName
  match tn
    TName(n, tp) -> TName(n, s |-> tp)

fun pat/(|->)(s: sub, p: pattern): pure pattern
  match p
    PatVar(tn, pat) -> PatVar(s |-> tn, s |-> pat)
    PatCon(tn, args, repr, targs, exists0, tres,  conInfo, skip) ->
      val sub' = s.remove(exists0)
      PatCon(s |-> tn, sub' |-> args, repr, sub' |-> targs, exists0, sub' |-> tres, conInfo, skip)
    PatWild -> PatWild
    PatLit(l) -> PatLit(l)

fun expr/(|->)(s: sub, e: expr): pure expr
  match e
    Lam(tn, eff, e) -> Lam(s |-> tn, s |-> eff, s |-> e)
    Var(tn, x) -> Var(s |-> tn, x)
    App(a, b) -> App(s |-> a, s |-> b)
    TypeLam(tvs, e) -> 
      val sub' = s.remove(tvs)
      TypeLam(tvs, sub' |-> e)
    TypeApp(e, tp) -> TypeApp(s |-> e, s |-> tp)
    Con(tn, repr) -> Con(s |-> tn, repr)
    ELit(l) -> ELit(l)
    Let(defGroups, e) -> Let(defGroups.map(fn(dg) s |-> dg), s |-> e)
    Case(es, bs) -> Case(s |-> es, bs.map(fn(b) s |-> b))

fun dg/(|->)(s: sub, dg: defGroup): pure defGroup
  match dg
    DefRec(defs) -> DefRec(defs.map(fn(d) s |-> d))
    DefNonRec(e) -> DefNonRec(s |-> e)

fun def/(|->)(s: sub, Def(name, scheme, expr, vis, isVal, inl, nameRng, doc): def): pure def
  Def(name, s |-> scheme, s |-> expr, vis, isVal, inl, nameRng, doc)

fun branch/(|->)(s: sub, Branch(p, e): branch): pure branch
  val sub' = s.remove(p.boundTypeVars)
  Branch(s |-> p, sub' |-> e)

fun guard/(|->)(s: sub, g: guard): pure guard
  match g
    Guard(e, e2) -> Guard(s |-> e, s |-> e2)

// TODO: More
fun freshTypeVar(k: kind, fl: flavour)
  val idbase = match fl
    Meta -> "_v"
    Skolem -> "$v"
    Bound -> "v"
  val id = unique-id(idbase)
  TypeVar(id, k, fl)

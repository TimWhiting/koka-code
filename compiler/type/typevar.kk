import compiler/type/type
import newstd/data/linearset
import newstd/data/linearmap
import compiler/core/core
import compiler/type/kind
import compiler/kind/kind
import compiler/common/syntax

alias tvs = linearSet<typeVar>
alias sub = linearMap<typeVar, ktype>

val typeVarEq = fn(tv1: typeVar, tv2: typeVar) tv1 == tv2
val typeVarShow = fn(tv: typeVar) tv.show
val emptyTvs = linearSet([], typeVarEq, typeVarShow)

val typeEq= fn(tp1: ktype, tp2: ktype) tp1 == tp2
val emptySub = linearMap([], typeVarEq, typeEq, typeVarShow, show)

fun subNew(l: list<(typeVar, ktype)>): exn sub
  if l.all(fn((tv, t)) tv.kind == t.kind) then
    linearMap(l, typeVarEq, typeEq, typeVarShow, show)
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
  if tau.freeTypeVars.member(tvar) then
    throw("type/typevar: subSingle: recursive type " ++ tvar.show)
  if tau.kind != tvar.kind then
    throw("type/typevar: subSingle: kind mismatch " ++ tau.show ++ " " ++ tvar.show)
  linearMap([(tvar, tau)], typeVarEq, typeEq, typeVarShow, show)

fun subLookup(s: sub, tv: typeVar): maybe<tau>
  s.maybeGet(tv)

fun subRemove(s: sub, tvars: list<typeVar>): sub
  s.removeAll(tvars)

fun subFind(s: sub, tv: typeVar): exn tau
  s.get(tv)

fun (+)(s1: sub, s2: sub): pure sub
  s1.subCompose(s2)

fun subCompose(s1: sub, s2: sub): pure sub
  s1.union(s1 |-> s2)

fun (|->)(s1: sub, s2: sub): pure sub
  s2.map(fn(k, v) (k, s1 |-> v))

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


fun single(tv: typeVar) 
  linearSet([tv], typeVarEq, typeVarShow)

fun tvsNew(tv: list<typeVar>) 
  linearSet(tv, typeVarEq, typeVarShow)

fun freeTypeVars(preds: list<pred>): pure tvs
  preds.foldl(emptyTvs, fn(acc: tvs, p: pred) acc + p.freeTypeVars)

fun freeTypeVars(pred: pred): pure tvs
  match pred
    PredSub(sub, super) -> sub.freeTypeVars + super.freeTypeVars
    PredIFace(_, args) -> args.map(freeTypeVars).unions

fun freeTypeVars(tp: ktype): pure tvs
  match tp
    TForAll(vars, preds, t) -> (t.freeTypeVars + preds.freeTypeVars) - vars
    TFun(args, eff, res) -> args.map(fn(a) a.snd.freeTypeVars).unions + res.freeTypeVars + eff.freeTypeVars
    TCon -> emptyTvs
    TVar(tv) -> single(tv)
    TApp(t, args) -> t.freeTypeVars + args.map(fn(a) a.freeTypeVars).unions
    TSyn(_, xs, t) -> t.freeTypeVars + xs.map(freeTypeVars).unions

fun freeTypeVars(l: list<ktype>): pure tvs
  l.map(freeTypeVars).unions

fun freeTypeVars(es: list<expr>): pure tvs
  es.map(freeTypeVars).unions

fun freeTypeVars(e0: expr): pure tvs
  match e0
    Lam(tn, eff, e) -> tn.freeTypeVars + eff.freeTypeVars + e.freeTypeVars
    Var(tn) -> tn.freeTypeVars
    App(a, b) -> a.freeTypeVars + b.freeTypeVars
    TypeLam(tvs, e) -> e.freeTypeVars - tvs
    TypeApp(e, tp) -> e.freeTypeVars + tp.freeTypeVars
    Con(tn) -> tn.freeTypeVars
    ELit -> emptyTvs
    Let(defGroups, e) -> defGroups.map(freeTypeVars).unions + e.freeTypeVars
    Case(es, bs) -> es.freeTypeVars + bs.map(freeTypeVars).unions

fun freeTypeVars(dg: defGroup): pure tvs
  match dg
    DefRec(defs) -> defs.map(freeTypeVars).unions
    DefNonRec(e) -> freeTypeVars(e)

fun freeTypeVars(d: def): pure tvs
  d.ktype.freeTypeVars + d.defExpr.freeTypeVars

fun freeTypeVars(bs: branch): pure tvs
  match bs
    Branch(p, e) -> (e.freeTypeVars - p.boundTypeVars) + p.freeTypeVars

fun freeTypeVars(p: pattern): pure tvs
  match p
    PatVar(tn, pat) -> tn.freeTypeVars + pat.freeTypeVars
    PatCon(tn, args, _, targs, exists0, tres) ->
      (tn.freeTypeVars + args.freeTypeVars + targs.freeTypeVars + tres.freeTypeVars) - exists0
    PatWild -> emptyTvs
    PatLit(_) -> emptyTvs

fun freeTypeVars(ps: list<pattern>): pure tvs
  ps.map(freeTypeVars).unions

fun freeTypeVars(gds: list<guard>): pure tvs
  gds.map(freeTypeVars).unions

fun freeTypeVars(gd: guard): pure tvs
  match gd
    Guard(e, e2) -> e.freeTypeVars + e2.freeTypeVars

fun freeTypeVars(TName(_, tp): tName): pure tvs
  tp.freeTypeVars

fun freeTypeVars(l: list<tName>): pure tvs
  l.map(freeTypeVars).unions

fun boundTypeVars(p: pattern): pure tvs
  match p
    PatVar(tn, pat) -> tn.boundTypeVars + pat.boundTypeVars
    PatCon(tn, args, _, targs, exists0, tres) ->
      tn.boundTypeVars + args.boundTypeVars + targs.boundTypeVars + tres.boundTypeVars + exists0.tvsNew
    PatWild -> emptyTvs
    PatLit(_) -> emptyTvs

fun boundTypeVars(l: list<pattern>): pure tvs
  l.map(boundTypeVars).unions

fun boundTypeVars(l: list<ktype>): pure tvs
  l.map(boundTypeVars).unions

fun boundTypeVars(tp: ktype): pure tvs
  match tp
    TForAll(vars, preds, t) -> preds.freeTypeVars + t.boundTypeVars + vars
    TFun(args, eff, res) -> args.map(snd).boundTypeVars + res.boundTypeVars + eff.boundTypeVars
    TSyn(_, _, t) -> t.boundTypeVars
    TApp(t, arg) -> t.boundTypeVars + arg.boundTypeVars
    _ -> emptyTvs

fun boundTypeVars(TName(_, tp): tName): pure tvs
  tp.boundTypeVars


// TODO: More
fun freshTypeVar(k: kind, fl: flavour)
  val idbase = match fl
    Meta -> "_v"
    Skolem -> "$v"
    Bound -> "v"
  val id = uniqueId(idbase)
  TypeVar(id, k, fl)

import compiler/type/type
import newstd/data/linearset
import compiler/common/range
import compiler/core/core

alias tvs = linearSet<typeVar>

val typeVarEq = fn(tv1: typeVar, tv2: typeVar) tv1 == tv2
val typeVarShow = fn(tv: typeVar) tv.show
val empty = linearSet([], typeVarEq, typeVarShow)

fun single(tv: typeVar) 
  linearSet([tv], typeVarEq, typeVarShow)

fun tvsNew(tv: list<typeVar>) 
  linearSet(tv, typeVarEq, typeVarShow)

fun freeTypeVars(preds: list<pred>): pure tvs
  preds.foldl(empty, fn(acc: tvs, p: pred) acc + p.freeTypeVars)

fun freeTypeVars(pred: pred): pure tvs
  match pred
    PredSub(sub, super) -> sub.freeTypeVars + super.freeTypeVars
    PredIFace(_, args) -> args.map(freeTypeVars).unions

fun freeTypeVars(tp: ktype): pure tvs
  match tp
    TForAll(vars, preds, tp) -> (tp.freeTypeVars + preds.freeTypeVars) - vars
    TFun(args, eff, res) -> args.map(fn(a) a.snd.freeTypeVars).unions + res.freeTypeVars + eff.freeTypeVars
    TCon -> empty
    TVar(tv) -> single(tv)
    TApp(tp, args) -> tp.freeTypeVars + args.map(fn(a) a.freeTypeVars).unions
    TSyn(_, xs, tp) -> tp.freeTypeVars + xs.map(freeTypeVars).unions

fun freeTypeVars(l: list<ktype>): pure tvs
  l.map(freeTypeVars).unions

fun freeTypeVars(es: list<expr>): pure tvs
  es.map(freeTypeVars).unions

fun freeTypeVars(expr: expr): pure tvs
  match expr
    Lam(tname, eff, e) -> tname.freeTypeVars + eff.freeTypeVars + e.freeTypeVars
    Var(tname) -> tname.freeTypeVars
    App(a, b) -> a.freeTypeVars + b.freeTypeVars
    TypeLam(tvs, e) -> e.freeTypeVars - tvs
    TypeApp(e, tp) -> e.freeTypeVars + tp.freeTypeVars
    Con(tname) -> tname.freeTypeVars
    ELit -> empty
    Let(defGroups, e) -> defGroups.map(freeTypeVars).unions + e.freeTypeVars
    Case(es, bs) -> es.freeTypeVars + bs.map(freeTypeVars).unions

fun freeTypeVars(dg: defGroup): pure tvs
  match dg
    DefRec(defs) -> defs.map(freeTypeVars).unions
    DefNonRec(def) -> freeTypeVars(def)

fun freeTypeVars(d: def): pure tvs
  d.ktype.freeTypeVars + d.expr.freeTypeVars

fun freeTypeVars(bs: branch): pure tvs
  match bs
    Branch(p, e) -> (e.freeTypeVars - p.boundTypeVars) + p.freeTypeVars

fun freeTypeVars(p: pattern): pure tvs
  match p
    PatVar(tname, pat) -> tname.freeTypeVars + pat.freeTypeVars
    PatCon(tname, args, _, targs, exists0, tres) ->
      (tname.freeTypeVars + args.freeTypeVars + targs.freeTypeVars + tres.freeTypeVars) - exists0
    PatWild -> empty
    PatLit(_) -> empty

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
    PatVar(tname, pat) -> tname.boundTypeVars + pat.boundTypeVars
    PatCon(tname, args, _, targs, exists0, tres) ->
      tname.boundTypeVars + args.boundTypeVars + targs.boundTypeVars + tres.boundTypeVars + exists0.tvsNew
    PatWild -> empty
    PatLit(_) -> empty

fun boundTypeVars(l: list<pattern>): pure tvs
  l.map(boundTypeVars).unions

fun boundTypeVars(l: list<ktype>): pure tvs
  l.map(boundTypeVars).unions

fun boundTypeVars(tp: ktype): pure tvs
  match tp
    TForAll(vars, preds, tp) -> preds.freeTypeVars + tp.boundTypeVars + vars
    TFun(args, eff, res) -> args.map(snd).boundTypeVars + res.boundTypeVars + eff.boundTypeVars
    TSyn(_, _, tp) -> tp.boundTypeVars
    TApp(tp, arg) -> tp.boundTypeVars + arg.boundTypeVars
    _ -> empty

fun boundTypeVars(TName(_, tp): tName): pure tvs
  tp.boundTypeVars
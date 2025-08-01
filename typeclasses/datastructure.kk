import std/num/float64
import std/core-extras

struct typeVar
  name: string;

struct typeConstructor
  name: string;

type literal
  BoolL(b: bool)
  IntL(i: int)
  CharL(c: char)
  FloatL(f: float64)

type ttype
  TVar(typeVar: typeVar)
  TApp(typeConstructor: typeConstructor, args: list<ttype>)
  TFun(t0: ttype, t1: ttype)
  ErrorT;

type typePred
  TPred(preds: list<(ident,ttype)>, tp: ttype)

type typeScheme
  ForAll(vars: list<typeVar>, tp: typePred)

struct ident
  name: string
  signature: maybe<typeScheme> = Nothing;

div type expr
  ELit(v: literal, tp: maybe<typeScheme> = Nothing)
  ETup(e0: list<expr>, tp: maybe<typeScheme> = Nothing)
  EVar(ident: ident, tp: maybe<typeScheme> = Nothing)
  App(e0: expr, e1: expr, tp: maybe<typeScheme> = Nothing)
  Lam(ident: ident, e: expr, tp: maybe<typeScheme> = Nothing)
  PrimOp(ident: ident, e: (evalue) -> exn evalue, tp: typeScheme)
  Let(ident: ident, e0: expr, e1: expr, tp: maybe<typeScheme> = Nothing)
  Over(ident: ident, cond: typeScheme, e: expr)
  Inst(ident: ident, cond: typeScheme, e0: expr, e1: expr);

div type evalue
  Bool(b: bool)
  Int(i: int)
  Char(c: char)
  Float(f: float64)
  Tuple(vals: list<evalue>)
  Clos(arg: ident, body: expr, env: list<(ident, evalue)>)
  PrimClos(body: (evalue) -> exn evalue);

alias environment = list<(ident, evalue)>

alias typeEnv = list<(ident, typeScheme)>

alias subst = list<(typeVar, typeScheme)>

type assumption
  Overloaded(ident: ident, t: typeScheme)
  Instance(ident: ident, t: typeScheme, newIdent: ident)
  Variable(ident: ident, t: typeScheme, newIdent: ident)

alias assumptions = list<assumption>

// Helper functions for stringifying datatypes
fun lit/show(v: literal): string
  match v
    BoolL(b) -> b.show
    IntL(i) -> i.show
    CharL(c) -> c.show
    FloatL(f) -> f.show

fun ttp/show(t: ttype): div string
  match t
    TVar(typeVar) -> typeVar.name
    TApp(typeConstructor, args) -> 
      typeConstructor.name ++
      (if args.is-empty then "" else "(" ++ args.map(fn(x) x.show).join(",") ++ ")")
    TFun(t0, t1) -> "(" ++ t0.show ++ " -> " ++ t1.show ++ ")"
    ErrorT -> "ErrorT"

fun mt/show(t: maybe<ttype>): div string
  match t
    Just(t0) -> t0.show
    Nothing -> "unknown"

fun tpred/show(TPred(preds, t): typePred): div string
  preds.map(fn(x:(ident,ttype)) x.fst.name ++ "::" ++ show(x.snd)).join(".") ++ t.show

fun scheme/show(ForAll(vars, t): typeScheme): div string
  if vars.is-empty then t.show
  else "forall " ++ vars.map(fn(x) x.name).join(",") ++ ". " ++ t.show

fun mscheme/show(t: maybe<typeScheme>): div string
  match t
    Just(t0) -> t0.show
    Nothing -> "??"

fun ident/show(t: ident): div string
  match t.signature
    Just(t0) -> t.name ++ "::" ++ t0.show
    Nothing -> t.name

fun expr/show(e: expr): div string
  match e
    ELit(value, t) -> "(Lit " ++ value.show ++ ": " ++ t.mscheme/show ++ ")"
    ETup(es, t) -> "(" ++ es.foldl("", fn(acc, i) acc ++ i.show ++ ",") ++ ")" ++ " : " ++ t.mscheme/show
    EVar(ident, t) -> ident.show ++ ": " ++ t.mscheme/show
    App(e0, e1, t) -> "\n(" ++ e0.show ++ " " ++ e1.show ++ ")" ++ ": " ++ t.mscheme/show
    Lam(ident, e0, t) -> "\n(\\" ++ ident.name ++ "." ++ e0.show ++ ": " ++ t.mscheme/show ++ ")"
    PrimOp(ident, _, t) -> "(Primitive " ++ ident.name ++ ": " ++ t.show ++ ")"
    Let(ident, e0, e1, t) -> "\n(let " ++ ident.show ++ " = " ++ e0.show ++ " in " ++ e1.show ++ ": " ++ t.mscheme/show ++ ")"
    Over(ident, cond, e0) -> "\nover " ++ ident.name ++ " " ++ cond.show ++ " " ++ e0.show
    Inst(ident, cond, e0, e1) -> "\ninst " ++ ident.name ++ " " ++ cond.show ++ " " ++ e0.show ++ " " ++ e1.show

fun evalue/show(v: evalue): div string
  match v
    Bool(b) -> b.show
    Int(i) -> i.show
    Char(c) -> c.show
    Float(f) -> f.show
    Tuple(vals) -> "(" ++ vals.foldl("", fn(acc, i) -> acc ++ i.show ++ ",") ++ ")"
    Clos(arg, body, env) -> "Clos(" ++ arg.name.show ++ ", " ++ body.show ++ ", " ++ show-env(env) ++ ")"
    PrimClos(_) -> "Primitive Operation"

fun show-env(l: environment): div string
  if l.is-empty then "Environment: ()" else
    "Environment: (\n\t" ++ l.map(fn(x) x.fst.name ++ " = " ++ x.snd.show).join("\n\t") ++ ")\n"

fun tpenv/show(l: typeEnv): div string
  if l.is-empty then "Type Environment: ()" else
    "Type Environment: (\n\t" ++ l.map(fn(x) x.fst.name ++ " = " ++ x.snd.show).join("\n\t") ++ ")\n"

fun subs/show(s: subst): div string
  "Substitutions: (\n\t" ++ s.map(fn (x) x.fst.name ++ " ==> " ++ x.snd.show).join("\n\t") ++ ")\n"

fun assums/show(s: assumptions): div string
  "Assumptions: (\n\t" ++ s.map(show).join("\n\t") ++ ")\n"

fun assum/show(a: assumption): div string
  match a
    Overloaded(ident, t) -> "Overloaded " ++ ident.name ++ " " ++ t.show
    Instance(ident, t, newIdent) -> "Instance " ++ ident.name ++ " " ++ t.show ++ " " ++ newIdent.name
    Variable(ident, t, newIdent) -> "Variable " ++ ident.name ++ " " ++ t.show ++ " " ++ newIdent.name

fun tup/show(x: (a,b), showA: (a) -> e string, showB: (b) -> e string): e string
  showA(x.fst) ++ "," ++ showB(x.snd)

fun tv/(==)(a: typeVar, b: typeVar): bool
  a.name == b.name

fun tc/(==)(a: typeConstructor, b: typeConstructor): bool
  a.name == b.name

fun tt/(==)(t1: ttype, t2: ttype): div bool
  match (t1, t2)
    (TVar(a), TVar(b)) -> a == b
    (TApp(a, aas), TApp(b, bs)) -> a == b && aas == bs
    (TFun(a, b), TFun(c, d)) -> a == c && b == d
    (ErrorT, ErrorT) -> True
    _ -> False

fun tpscheme/(==)(t1: typeScheme, t2: typeScheme): div bool
  match (t1, t2)
    (ForAll(aas, a), ForAll(bs, b)) -> aas == bs && a == b

fun tpred/(==)(t1: typePred, t2: typePred): div bool
  match (t1, t2)
    (TPred(aas, a), TPred(bs, b)) -> aas == bs && a == b 

fun ident/(==)(i1: ident, i2: ident): div bool
  match (i1, i2)
    (Ident(a, sa), Ident(b, sb)) -> 
      val nameMatch = a == b
      val sigMatch = match (sa, sb)
        (Nothing, Nothing) -> True
        (Just(sa1), Just(sb1)) -> sa1 == sb1
        _ -> False
      // trace("Name match " ++ nameMatch.show ++ " sig match " ++ sigMatch.show)
      nameMatch && sigMatch



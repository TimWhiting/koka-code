import datastructure

// Type Constructors
val tCInt = TypeConstructor("int")
val tCChar = TypeConstructor("char")
val tCFloat = TypeConstructor("float")
val tcTuple = TypeConstructor("Tuple")
val tCBool = TypeConstructor("bool")
val tInt = TApp(tCInt, [])
val tChar = TApp(tCChar, [])
val tFloat = TApp(tCFloat, [])
val tBool = TApp(tCBool, [])

fun tupleT(types: list<ttype>): ttype
  TApp(tcTuple, types)

// Get typeScheme from expression
fun typeOf(e: expr): maybe<ttype>
  match e
    ELit(_, t) -> Just(t.typeOf)
    ETup(_, t) -> Just(t.typeOf)
    EVar(_, t) -> Just(t.typeOf)
    App(_, _, t) -> Just(t.typeOf)
    Lam(_, _, t) -> Just(t.typeOf)
    Let(_, _, _, t) -> Just(t.typeOf)
    PrimOp(_, _, t) -> Just(t.typeOf)
    _ -> Nothing

fun typePredOf(e: expr): maybe<typePred>
  match e
    ELit(_, t) -> Just(t.typePred)
    ETup(_, t) -> Just(t.typePred)
    EVar(_, t) -> Just(t.typePred)
    App(_, _, t) -> Just(t.typePred)
    Lam(_, _, t) -> Just(t.typePred)
    Let(_, _, _, t) -> Just(t.typePred)
    PrimOp(_, _, t) -> Just(t.tp)
    _ -> Nothing

fun typeSchemeOf(e: expr): maybe<typeScheme>
  match e
    ELit(_, t) -> t
    ETup(_, t) -> t
    EVar(_, t) -> t
    App(_, _, t) -> t
    Lam(_, _, t) -> t
    Let(_, _, _, t) -> t
    PrimOp(_, _, t) -> Just(t)
    _ -> Nothing

fun updateType(e: expr, t: maybe<typeScheme>): expr
  match e
    ELit(l, _) -> ELit(l, t)
    ETup(l, _) -> ETup(l, t)
    EVar(l, _) -> EVar(l, t)
    App(l, r, _) -> App(l, r, t)
    Lam(l, r, _) -> Lam(l, r, t)
    Let(l, r, b, _) -> Let(l, r, b, t)
    _ -> e

fun getPred(t: maybe<typeScheme>): maybe<typeScheme>
  match t
    Just(ForAll(_, TPred(Cons((_, t1), _), _))) -> Just(ForAll([], TPred([], t1)))
    _ -> Nothing

fun removePred(i: ident): ident
    Ident(i.name, i.signature.removePred)

fun removePred(t: maybe<typeScheme>): maybe<typeScheme>
  match t
    Just(ForAll(vars, TPred(_, tp))) -> Just(ForAll(vars, TPred([], tp)))
    _ -> t

fun addPred(t: typePred, p: (ident, ttype)): typePred
  match t
    TPred(preds, tp) -> TPred(Cons(p, preds), tp)

fun typePred(t: maybe<typeScheme>): typePred
  match t
    Just(x) -> x.tp
    Nothing -> ErrorT.pred

fun typeOf(t: typeScheme): ttype
  t.tp.tp

fun typeOf(t: maybe<typeScheme>): ttype
  match t
    Just(x) -> x.tp.tp
    Nothing -> ErrorT

// Helper functions for creating types
fun scheme(t: typePred, vars: list<typeVar> = []): typeScheme
  ForAll([],t)

fun scheme(t: ttype, vars: list<typeVar> = []): typeScheme
  ForAll(vars, TPred([], t))

fun pred(t: ttype, vars: list<(ident, ttype)> = []): typePred
  TPred(vars, t)

// Helper functions for creating expressions
fun eInt(i: int): expr
  ELit(IntL(i), Just(tInt.scheme))

fun eChar(c: char): expr
  ELit(CharL(c), Just(tChar.scheme))

fun eBool(c: bool): expr
  ELit(BoolL(c), Just(tBool.scheme))

fun eFloat(c: float64): expr
  ELit(FloatL(c), Just(tFloat.scheme))

fun ident(name: string): ident
  Ident(name)

fun eVar(name: string): expr
  EVar(Ident(name), Nothing)

// A class type is just a list of the types of the functions that make it up
fun classT(types: list<ttype>): ttype
  TApp(tcTuple, types)

fun classT(t: ttype): ttype
  TApp(tcTuple, [t])

fun createEqType(t: ttype): ttype
  TFun([t,t].tupleT,tBool)

fun createBinaryOpType(t: ttype): ttype
  TFun([t,t].tupleT,t)

fun envFreeVars(env: typeEnv): list<typeVar>
  env.flatmap(fn(x) x.snd.freeVars)

fun freeVars(t: typeScheme): list<typeVar>
  var res := Nil
  val _ = t.map fn (x)
    match x
      TVar(a) -> 
        match t.vars.find(fn(xx) xx == a) 
          Nothing -> x
          Just(aa) -> 
            res := Cons(aa, res)
            x
      _ -> x
  res

fun freeVars(TPred(l, t): typePred, env: typeEnv): div list<typeVar>
  l.map(fn (x) x.snd.freeVars(env)).flatmap(fn (x) x) ++ t.freeVars(env)

fun freeVars(t: ttype, env: typeEnv): div list<typeVar>
  match t
    TVar(a) -> 
      match envFreeVars(env).find(fn(x) x == a) 
        Just(_) -> []
        _ -> [a]
    TApp(_, b) -> b.flatmap(fn (x) x.freeVars(env))
    TFun(a, b) -> a.freeVars(env) ++ b.freeVars(env)
    ErrorT -> []

fun map(t: typeScheme, f: (ttype) -> e ttype): e typeScheme
  match t
    ForAll(vars, t1) -> ForAll(vars, t1.map(f))

fun map(t: typePred, f: (ttype) -> e ttype): e typePred
  match t
    TPred(preds, t1) -> TPred(preds.map(fn(x) (x.fst, f(x.snd))), f(t1))
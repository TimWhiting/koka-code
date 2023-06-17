import datastructure
import utils

linear effect newType
  fun nextTypeVar(): ttype

linear effect exit
  fun shouldExit(): bool
  fun setExit(x: bool): ()

fun genTypeVars(f: () -> <newType|e> a): e a
  var typeVarNum := 0
  with handler
    fun nextTypeVar()
      typeVarNum := typeVarNum + 1
      TVar(TypeVar("tVar" ++ typeVarNum.show))
  f()

fun handleExit(f: () -> <exit|e> a): e a
  var s := False
  with handler
    fun shouldExit() s
    fun setExit(x) s := x
  f()

fun doInfer(x: expr, env: typeEnv = [], assums: assumptions = []): <div,exn> (expr, subst)
  with handleExit // Custom error handling to report error from innermost expression
  with genTypeVars // Generate fresh type variables
  val (res, sub) = infer(x, env, assums)
  // trace(sub.show)
  (applyAll(res, sub), sub)
  // (res, sub)

fun infer(x: expr, env: typeEnv = [], assums: assumptions = []): <div,exit,exn,newType> (expr, subst)
  with handler // Catch errors from unification, but only report error from innermost expression
    fun throw-exn(e)
      if shouldExit() then
        throw-exn(e)
      else
        setExit(True)
        throw("Error inferring type of " ++ x.show ++ "\n" ++ env.show ++ "\n" ++ assums.show ++ "\n\tInner error " ++ e.message)
  val y = match x
    ELit(v,t) -> (ELit(v,t), [])
    ETup(v,_) -> 
      val (v1, s1) = v.map(fn (vi) infer(vi, env, assums)).unzip
      val t = v1.map(fn (vi) typeOf(vi).default(ErrorT))
      // trace("Compose tuple " ++ t.foldl("", fn (acc, a) acc ++ a.show ++ " "))
      (ETup(v1, Just(tupleT(t).scheme)), s1.foldl([], fn (acc, a) acc.compose(a)))
    EVar(x1,_) -> 
      match env.find(fn(a) a.fst.name == x1.name)
        Just((_, t)) -> (EVar(x1, Just(t.instantiate().scheme)), [])
        Nothing -> 
          match assums.find(fn(a) over(a, x1))
            Just(Overloaded(i, t)) -> 
              // trace("Used overloaded identifier for " ++ x.show ++ " with type " ++ t.show)
              val xt = t.instantiatePred(i).scheme
              // trace("Instantiated to " ++ xt.show)
              (EVar(x1, Just(xt)), [])
            Nothing -> throw("Unbound variable " ++ x1.name ++ " in environment " ++ env.show)
            _ -> throw("Did not find instance")
    // Needed to instantiate in order to allow for type variables in a primitive op to unify with different types 
    // This would happen in the var case if the operations were variables. 
    PrimOp(a,b,c) -> (PrimOp(a,b,c.instantiate().scheme), [])
    // Abs: checked
    Lam(i, e, _) -> 
      val tv = nextTypeVar()
      val newEnv = Cons((i, tv.scheme), env)
      val (e1, s1) = infer(e, newEnv, assums)
      val newTv = apply(s1, tv.scheme)
      val t = TFun(newTv.tp.tp, typeOf(e1).default(ErrorT))
      (Lam(i, e1, Just(t.scheme)), s1)
    // Comb: checked
    App(f, v, _) ->
      val tv = nextTypeVar()
      // TODO: Handle explicit type annotation with predicates
      val (f1, s1) = infer(f, env, assums)
      match typeSchemeOf(f1)
        Nothing -> throw("Cannot infer type of function " ++ f1.show)
        Just(type1) -> 
          val env1 = apply(s1, env)
          val (rh, s2) = infer(v, env1, assums)
          match typeSchemeOf(rh)
            Nothing -> throw("Cannot infer type of argument " ++ rh.show)
            Just(type2) -> 
              // match f
              //   PrimOp() -> trace("Applying primitive operation " ++ f.show ++ " with inferred type " ++ f1.show ++ " to " ++ rh.show ++ " with type " ++ type2.show)
              //   _ -> trace("Applying operation " ++ f1.show ++ " to " ++ rh.show ++ " with type " ++ type2.show)
              val s3 = unify(apply(s2, type1), TFun(type2.typeOf, tv).scheme)
              // trace("Compose app\n" ++ s1.show ++ "\ns2 " ++ s2.show ++ "\ns3" ++ s3.show)
              val finalSub = s1.compose(s2).compose(s3) // TODO: Is this the right order?

              val t = apply(finalSub, tv.scheme)
              val newFT = match f1.typeSchemeOf
                Just(f2) -> Just(apply(finalSub, f2))
                Nothing -> f1.typeSchemeOf
              val newRH = rh.updateType(apply(finalSub, Just(rh.typeSchemeOf.default(ErrorT.scheme))))
              // match f
              //   PrimOp() -> trace("Unified to " ++ newFT.show ++ " applied to " ++ newRH.typeSchemeOf.show ++ " with result type " ++ t.show ++ "\n")
              //   _ -> trace("Unified to " ++ newFT.show ++ " applied to " ++ newRH.typeSchemeOf.show ++ " with result type " ++ t.show ++ "\n")
              (App(f1.updateType(newFT), newRH, Just(t)), finalSub)
    // Let: checked
    Let(i, e, b, _) ->
      val (e1, s1) = infer(e, env, assums)
      val e1Ty = e1.typePredOf.default(ErrorT.pred).generalize(apply(s1, env))
      val env1 = Cons((i, e1Ty), env)
      val env2 = apply(s1, env1)
      val (b1, s2) = infer(b, env2, assums)
      (Let(i, e1, b1, b1.typeSchemeOf), s1.compose(s2))
    // Over: checked
    Over(i, c, e) ->
      infer(e, env, Cons(Overloaded(i,c), assums)) // The translation replaces Over with the translation of e
    // Inst: checked
    Inst(i, c, e0, e1) -> 
      // Check to see if the instance conflicts with any already there, (uses declared type)
      match assums.find(fn(a) fits(a, i, c))
        Just(_) ->
          // Assuming that the instance has a typed signature
          // Infer the expression
          val (newE0, sub) = infer(e0, env, assums)
          val e0Ty = newE0.typePredOf.default(ErrorT.pred).generalize(apply(sub, env))
          // Add to assumption list
          val newIdent = i(signature=Just(e0Ty))
          // Check to see if the instance conflicts with any already there, (uses inferred type)
          match assums.find(fn(a) fits(a, i, e0Ty)) 
            Just(_) -> 
              val newAssums = Cons(Instance(i, c, newIdent), assums)
              val (newE1, sub1) = infer(e1, env, newAssums)
              // Convert to a let with a translated identifier
              val res = Let(newIdent, newE0.updateType(Just(e0Ty)), newE1, newE1.typeSchemeOf)
              (res, sub.compose(sub1))
            _ -> throw("Cannot instantiate " ++ i.name ++ " with " ++ e0Ty.show)
        _ -> throw("Cannot instantiate " ++ i.name ++ " with " ++ c.show)
  // match y.fst.typePredOf
  //   Just(TPred(Cons(_, _))) -> trace("Has Predicated type" ++ y.fst.show)
  //   Nothing -> ()
  match y.fst.typeSchemeOf
    Just(ForAll(_, TPred(Cons(pred, _)))) ->
      match assums.find(fn(a) inst(a, pred))
        Just(i) ->
          // trace("Found match for " ++ y.fst.show ++ " i " ++ i.show) 
          (Lam(i.ident, y.fst, Nothing), y.snd)
        Nothing -> y
    _ -> y

fun applyAll(e: expr, subs: subst): div expr
  match e
    ELit(v,t) -> ELit(v,t)
    ETup(v,t) -> ETup(v.map(fn (vi) applyAll(vi, subs)), apply(subs, t))
    EVar(x1,t) -> EVar(x1, apply(subs, t))
    PrimOp(a,b,c) -> PrimOp(a,b,apply(subs,c))
    Lam(i, e1, t) -> Lam(i, applyAll(e1, subs), apply(subs, t))
    App(f, v, t) -> App(applyAll(f, subs), applyAll(v, subs), apply(subs, t))
    Let(i, e1, b, t) -> Let(i, applyAll(e1, subs), applyAll(b, subs), apply(subs, t))
    Over(i, c, e1) -> Over(i, c, applyAll(e1, subs))
    Inst(i, c, e0, e1) -> Inst(i, c, applyAll(e0, subs), applyAll(e1, subs))

fun (===)(t1: typeScheme, t2: typeScheme): <div,newType> bool
  match (t1, t2)
    (ForAll(aas, a), ForAll(bs, b)) ->
      if aas.length != bs.length then False else
        val subs = aas.zip(bs).foldl([]) fn(acc, x)
          val y = nextTypeVar().scheme
          Cons((x.fst, y), Cons((x.snd, y), acc))
        apply(subs, a.scheme) == apply(subs, b.scheme)

fun over(assum: assumption, id: ident): bool
  match assum
    Overloaded(i, _) -> i.name == id.name
    Instance(_, _, _) -> False
    Variable(_, _, _) -> False

fun inst(assum: assumption, pred: (ident,ttype)): bool
  match assum
    Overloaded(_, _) -> False
    Instance(i, t, _) ->
      unsafe-total
        // trace("Checking " ++ i.show ++ t.show ++ " against " ++ pred.fst.show ++ pred.snd.show ++ "\n")
        i == pred.fst && t.tp.tp == pred.snd
    Variable(i, t, _) -> 
      unsafe-total
        i == pred.fst && t.tp.tp == pred.snd

fun fits(assum: assumption, id: ident, t: typeScheme): bool
  match assum
    Overloaded(i, _) -> i.name == id.name
    Instance(_, _, _) -> False
    Variable(_, _, _) -> False

fun doesUnify(t1: ttype, t2: ttype): div bool
  with handler
    final ctl throw-exn(e)
      False
  unify(t1, t2)
  True

fun unify(t1: typeScheme, t2: typeScheme): <div,exn> subst
  // trace("Attempting to unify " ++ t1.show() ++ " with " ++ t2.show())
  with handler
    final ctl throw-exn(e)
      trace("Failed to unify " ++ t1.show() ++ " with " ++ t2.show() ++ " because of " ++ e.message)
      throw-exn(e)
  val result = match (t1, t2)
    (ForAll(_, b), ForAll(_, d)) -> unify(b, d)
  // trace("Found substitution " ++ result.show())
  result

fun unify(t1: typePred, t2: typePred): <div,exn> subst
  match (t1, t2)
    (TPred(_, tt1), TPred(_, tt2)) -> 
      unify(tt1, tt2)

// TODO: I need to be consistent about which side to add to the substitution
fun unify(t1: ttype, t2: ttype): <div,exn> subst
  match (t1, t2)
    (TVar(a), TVar(b)) -> if a == b then [] else [(a, t2.scheme), (b, t1.scheme)]
    (TVar(a), _) -> 
      match t2.freeVars([]).find(fn (x) x == a)
        Just(_) -> throw("Occurs check failed")
        Nothing -> [(a, t2.scheme)]
    (_, TVar(a)) -> 
      match t1.freeVars([]).find(fn (x) x == a)
        Just(_) -> throw("Occurs check failed")
        Nothing -> [(a, t1.scheme)]
    (TApp(a, b), TApp(c, d)) -> 
      if a == c then b.zip(d).map(fn (x) unify(x.fst, x.snd)).foldl([], fn (acc, x) acc.compose(x))
      else throw("Cannot unify " ++ t1.show() ++ " with " ++ t2.show())
    (TFun(a, b), TFun(c, d)) -> 
      val subst = unify(a, c)
      unify(apply(subst, b), apply(subst, d)).compose(subst)
    (ErrorT, _) -> []
    (_, ErrorT) -> []
    _ -> throw("Cannot unify " ++ t1.show() ++ " with " ++ t2.show())

// Generalize
fun generalize(t: typePred, env: typeEnv): div typeScheme
  t.scheme(t.freeVars(env))

// Takes care of typePred
fun instantiate(t: typeScheme): <div,newType> typePred
  match t
    ForAll(vars, t1) -> 
      val vars' = vars.map(fn (x) nextTypeVar())
      val s = vars.zip(vars').map(fn (x) (x.fst, x.snd))
      t1.map(fn(t2) t2.replace(s))

fun instantiatePred(t: typeScheme, n: ident): <div,newType> typePred
  match t
    ForAll(vars, t1) -> 
      val vars' = vars.map(fn (x) nextTypeVar())
      val s = vars.zip(vars').map(fn (x) (x.fst, x.snd))
      val t2 = t1.map(fn(t2) t2.replace(s))
      t2.addPred((n, t2.tp))

// Takes care of typePred
// Replace just is used for instantiation where we only care about replacing type variable with fresh variables
fun replace(t: ttype, l: list<(typeVar, ttype)>): div ttype
  match t
    TApp(a, b) -> TApp(a, b.map(fn (x) x.replace(l)))
    TFun(a, b) -> TFun(a.replace(l), b.replace(l))
    TVar(a) ->
      match l.find(fn (x) x.fst == a)
        Just((_, b)) -> b
        Nothing -> TVar(a)
    ErrorT -> ErrorT

// Apply replaces type variables in the predicates and types with the type from the substitution map
fun apply(s: subst, t: maybe<typeScheme>): div maybe<typeScheme>
  match t
    Just(a) -> Just(apply(s, a))
    Nothing -> Nothing
  
fun apply(s: subst, env: typeEnv): div typeEnv
  env.map(fn(x) (x.fst, apply(s, x.snd)))

fun apply(s: (typeVar, typeScheme), t: typeScheme): div typeScheme
  t.map(fn(x) apply(s, x))

fun apply(s: subst, t: typeScheme): div typeScheme
  s.foldl(t, fn(acc:typeScheme, x:(typeVar, typeScheme)) apply(x, acc))

fun apply(s: subst, t: ttype): div ttype
  s.foldl(t, fn(acc:ttype, x:(typeVar, typeScheme)) apply(x, acc))

fun apply(s: (typeVar, typeScheme), t: ttype): div ttype
  match t
    TApp(a, Nil) -> TApp(a, Nil)
    TVar(a) -> if a == s.fst then s.snd.typeOf else TVar(a)
    TApp(a, b) -> TApp(a, b.map(fn (x) apply(s, x)))
    ErrorT -> ErrorT
    TFun(t0, t1) -> TFun(apply(s, t0), apply(s, t1))

fun compose(s1: subst, s2: subst): div subst
  val s2' = s2.map(fn(x) (x.fst, apply(s1, x.snd)))
  // val s1' = s1.map(fn(x) (x.fst, apply(s2', x.snd)))
  s2' ++ s1 // Add s1 after s2 so that s1 takes precedence
  // if s1.is-empty || s2.is-empty then res else
  //   trace("Composing " ++ s1.show ++ " with " ++ s2.show)
  //   trace("Resulting in " ++ res.show)
  //   res

fun contains(l: list<a>, a: a, equal: (a,a) -> e bool): e bool
  l.foldl(False, fn(acc, x) x.equal(a) || acc)

fun greater(t1: typeScheme, t2: typeScheme, assums: assumptions): <exn,div> bool
  val fr = t1.freeVars
  val notFree = t2.vars.all(fn(x) fr.contains(x, fn(x1, x2) x1 == x2))
  // trace("Prior to unification: " ++ t1.show() ++ " and " ++ t2.show())
  // TODO: Is this what we are supposed to do here?
  // trace("Checking greater")
  val subs = try(fn() t1.unify(t2), fn(_) [])
  val newT1 = apply(subs, t1)
  val newT2 = apply(subs, t2)
  // trace("Post unification: " ++ newT1.show() ++ " and " ++ newT2.show())
  notFree && newT1.tp.greater(newT2.tp, assums)

// fun greater(t1: typeScheme, t2: ttype, assums: assumptions): <exn,div> bool
//   // TODO: This is a hack??
//   t1.tp.tp == t2

fun greater(t1: typePred, t2: typePred, assums: assumptions): <exn,div> bool
  match (t1, t2)
    (TPred(a, tt1), TPred(c, tt2)) -> 
      tt1 == tt2 && a.all(fn(x) c.contains(x, fn(x1, x2) x1 == x2) || assums.eliminates(x)) 

fun eliminates(assums: assumptions, t: (ident,ttype)): <exn,div> bool
  assums.any(fn(x) x.eliminates(t, assums))

fun eliminates(assum: assumption, t: (ident, ttype), assums: assumptions): <exn,div> bool
  match assum
    Overloaded(_, _) -> False
    Instance(i, ty, _) -> 
      t.fst.name == i.name && ty.greater(t.snd.scheme, assums)
    Variable(i, ty, _) ->
      t.fst.name == i.name && ty.tp.tp == t.snd

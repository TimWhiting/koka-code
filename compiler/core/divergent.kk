import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/core/uniquefy
import std/data/linearset

// Fix a group of recursive definitions to potentially include the divergence effect in their type
fun analyzeDivergence(defs0: list<def>)
  match defs0
    [] -> False
    Cons(_, Cons) -> True // For mutual recursion, we assume divergence for now
    [d0] ->
      val DefRec([d1]) = DefRec([d0]).uniquefy
      d1.isDivergent

// Is a recursive definition group potentially divergent?
// Assumes that the defintions are uniquefied
// A valid result is always to return 'True'
fun isDivergent(d: def): <comp-flags, pure> bool
  d.defExpr.isDivergentBody(d.def-name)

fun isDivergentBody(b: expr, dname: name)
  match b
    TypeLam(_, expr) -> expr.isDivergentBody(dname)
    TypeApp(expr) -> expr.isDivergentBody(dname)
    Lam(pars, _, e) -> e.isDivFun(pars, dname)
    _ -> True

fun isDivFun(b: expr, pars: list<tName>, dname: name): <comp-flags, pure> bool
  match pars
    Nil -> True
    _ ->
      val calls = runDiv(dname, pars, {divExpr(b)})
      val orders = calls.transpose.permutations.map(transpose)
      fun isAnOrder(cs)
        cs.all(fn(call) match call.drop-while(fn(c) c == SEq) {Cons(SLt) -> True; _ -> False})
      !orders.any(isAnOrder)

fun transpose(xss:list<list<a>>): pure list<list<a>>
  fun combine(y, h, ys, t)
    Cons(Cons(y, h), transpose(Cons(ys, t)))
  match xss
    Nil -> Nil
    Cons(Nil, xss') -> transpose(xss')
    Cons(Cons(x, xs), xss') -> 
      val (hds, tls) = xss'.map(fn(Cons(hd, tl)) (hd, tl)).unzip
      combine(x, hds, xs, tls)

fun permutations(xs0: list<a>): div list<list<a>>
  fun perms(xs, is)
    match xs
      Nil -> Nil
      Cons(t, ts) -> 
        fun interleave'(f, xs', r)
          match xs'
            Nil -> (ts, r)
            Cons(y, ys) ->
              val (us, zs) = interleave'(fn(x) f(Cons(y, x)), ys, r)
              (Cons(y, us), Cons(f(Cons(t, Cons(y, us))), zs))
        fun interleave(xs', r)
          interleave'(id, xs', r).snd
        is.permutations.foldr(perms(ts, Cons(t, is)), interleave)
  perms(xs0, Nil)

struct rel
  n: name
  ns: list<nameSet>
  ns': list<nameSet>

alias call = list<size>

type size
  SLt
  SEq
  Unknown

fun (==)(s1: size, s2: size): bool
  match (s1, s2)
    (SLt, SLt) -> True
    (SEq, SEq) -> True
    (Unknown, Unknown) -> True
    _ -> False

effect divergent
  val rel: rel
  fun addCall(n: name, c: call): ()

alias divEff = <divergent, comp-flags, pure>

fun setRel(r: rel, f: () -> divEff a): divEff a
  with override
    val rel = r
    fun addCall(n, c) addCall(n, c)
  f()

fun runDiv(dname: name, args: list<tName>, f: () -> divEff a): <comp-flags, pure> list<call>
  var calls: list<call> := []
  with handler
    val rel = Rel(dname, args.map(fn(a) namesEmpty + a.getName), args.map(fn(a) namesEmpty))
    fun addCall(n, c)
      calls := Cons(c, calls)
  f()
  calls

fun at(xs: list<nameSet>, i: int): nameSet
  xs[i].default(namesEmpty)

fun isRecursiveCall(n: name): divEff bool
  val Rel(rname) = rel
  rname == n

fun lookupSize(dname: name, argPos: int, argName: name): divEff size
  val Rel(rname, eqs, lts) = rel
  if rname != dname then Unknown
  else
    val equal = eqs.at(argPos)
    val lower = lts.at(argPos)
    if lower.member(argName) then SLt
    elif equal.member(argName) then SEq
    else Unknown

fun addRelation(sz: size, name1: name, name2: name, div: () -> divEff a): divEff a
  if sz == Unknown then div()
  else
    val Rel(rname, eqs, lts) = rel
    fun addEqLt(eq, lt)
      if eq.member(name1) then
        match sz
          SLt -> (eq, lt.add(name2))
          SEq -> (eq.add(name2), lt)
          _ -> fail("core/divergent addRelation: encountered Unknown")
      elif lt.member(name1) then
        (eq, lt.add(name2))
      else (eq, lt)
    val (eqs', lts') = eqs.zipwith(lts, addEqLt).unzip
    setRel(Rel(rname, eqs', lts'), div)

fun divExpr(e: expr): divEff ()
  match e
    Lam(_, _, expr) -> expr.divExpr
    // Ignore .open effect calls
    App(App(TypeApp(Var(openName)), [f]), args) | openName.getName == nameEffectOpen ->
      App(f, args).divExpr
    App(TypeApp(App(TypeApp(Var(openName)), [f]), targs), args) | openName.getName == nameEffectOpen ->
      App(TypeApp(f, targs), args).divExpr
    // applications
    App(TypeApp(v as Var), args) ->
      App(v, args).divExpr
    App(Var(tname), args) ->
      val isRec = isRecursiveCall(tname.getName)
      if isRec then
        val call = args.map-indexed(fn(i, a) argumentSize(tname.getName, i, a))
        addCall(tname.getName, call)
      else
        ()
      args.map(divExpr)
      ()
    Var(tname) -> // recursive call may appear as argument, say id(recfun)(x)
      val isRec = isRecursiveCall(tname.getName)
      if isRec then
        addCall(tname.getName, [Unknown])
      else
        ()
    App(f, args) ->
      f.divExpr
      args.map(divExpr)
      ()
    TypeLam(_, expr) -> expr.divExpr
    TypeApp(expr) -> expr.divExpr
    Let(dgs, expr) ->
      dgs.map(divDefGroup)
      expr.divExpr
    Case(exprs, branches) ->
      exprs.map(divExpr)
      branches.foreach(fn(br) divBranch(exprs, br))
    _ -> ()

fun divBranch(exprs, Branch(pats, guards): branch): divEff ()
  fun extractName(e: expr)
    match e
      Var(tname) -> Just(tname.getName)
      App(TypeApp(Var(sameSize)), [Var(tname)]) | namesSameSize.any(fn(x) x == sameSize.getName) ->
        Just(tname.getName)
      _ -> Nothing
  fun divGuard(Guard(test, expr))
    test.divExpr
    expr.divExpr
    ()
  exprs.map(extractName).zip(pats).foreach(fn((n, p)) divPattern(SEq, n, p))
  guards.foreach(fn(g) g.divGuard)

fun divPattern(size: size, mbName: maybe<name>, p: pattern): divEff ()
  match (mbName, p)
    (Just(n), PatVar(pname, pat)) ->
      with addRelation(size, n, pname.getName)
      divPattern(size, mbName, pat)
    (_, PatCon(_, pats, _, _, _, _, info)) ->
      pats.foreach(fn(p') divPattern(if info.typeSort.is-inductive then SLt else size, mbName, p'))
    (_, _) ->
      ()

fun divDefGroup(dg: defGroup): divEff ()
  match dg
    DefNonRec(d) -> d.divDef
    DefRec(dfs) -> dfs.foreach(divDef)

fun divDef(d: def)
  d.defExpr.divExpr

fun argumentSize(name: name, pos: int, arg: expr): divEff size
  fun reduceSize(sz)
    match sz
      SEq -> SLt
      _ -> sz
  match arg
    Var(tname, _) ->
      lookupSize(name, pos, tname.getName)
    // Ignore .open effect calls
    App(App(TypeApp(Var(openName)), [f]), args) | openName.getName == nameEffectOpen ->
      argumentSize(name, pos, App(f, args))
    App(TypeApp(App(TypeApp(Var(openName)), [f]), targs), args) | openName.getName == nameEffectOpen ->
      argumentSize(name, pos, App(TypeApp(f, targs), args))
    // special 'unsafeDecreasing' call
    App(TypeApp(Var(name'), [_]), [_]) | name'.getName == nameDecreasing ->
      SLt
    // special case substr1
    App(Var(substrName), Cons(Var(sname), _)) | substrName.getName == nameSubStr1 ->
      val sz = lookupSize(name, pos, sname.getName)
      reduceSize(sz)
    // these two cases state that the call to a function f where f < name is itself < name
    App(Var(tname)) ->
      lookupSize(name, pos, tname.getName)
    App(TypeApp(Var(tname))) ->
      lookupSize(name, pos, tname.getName)
    _ -> Unknown

  


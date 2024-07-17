import compiler/core/core
import compiler/common/name
import compiler/common/name-prim
import compiler/platform/config
import compiler/common/failure
import compiler/type/type
import compiler/common/syntax
import compiler/common/range

value type kexpr
  U(e: expr) // unchanged
  I(e: expr) // identity
  R(e: expr) // returned
  F(e: ((expr -> ureff expr) -> ureff expr)) // CPS Transformed, needs continuation

fun unreturn()
  with handler
    val currentEff = Nothing
  setCoreDefs(urTopDefGroups(getCoreDefs()))

fun urTopDefGroups(defGroups: list<defGroup>): ureff list<defGroup>
  defGroups.map(urTopDefGroup)

fun urTopDefGroup(dg: defGroup)
  match dg
    DefRec(defs) -> DefRec(defs.map(urTopDef))
    DefNonRec(d) -> DefNonRec(urTopDef(d))

fun urTopDef(d: def): ureff def
  val (makeDef, kexpr) = d.urDef
  match kexpr
    U(e) -> makeDef(e)
    I(e) -> makeDef(e)
    _ -> fail("core/unreturn urTopDef: should not happen: return inside top level definition")

effect ur
  val currentEff: maybe<keffect>

alias ureff = <ur,comp-flags,pure,corePhase,uniquePhase>

fun currentEffect(eff: keffect, k: () -> <ur|e> a): <ur|e> a
  with override
    val currentEff = Just(eff)
  k()

fun urDef(d: def)
  val kexpr = d.defExpr.urExpr
  (fn(e) d(defExpr = e), kexpr)

fun urExpr(e: expr): <comp-flags,corePhase,div,exn,ur,uniquePhase> kexpr
  match e
    // lambdas and type lambdas use UnK to contain returns inside their body
    Lam(pars, eff, body) ->
      with currentEffect(eff)
      e.emapUnK(fn(b) Lam(pars, eff, b), body.urExpr)
    TypeLam(tvars, body) ->
      e.emapUnK(fn(b) TypeLam(tvars, b), body.urExpr)
    // Type applicatoins may contain return (? todo check this)
    TypeApp(body, targs) ->
      Just(e).emapK(fn(b) TypeApp(b, targs), body.urExpr)
    // bindings
    Let(defgs, body) ->
      e.urLet(defgs, body.urExpr)
    // case: scrutinee cannot contain return due to grammar
    Case(scruts, branches) ->
      e.urCase(scruts, branches)
    // return
    App(Var(v), [arg]) | v.get-name == nameReturn -> R(arg)
    // pure expressions that do not contain return (as checked by the grammar)
    App(f, args) ->
      I(App(f.urPure, args.map(urPure)))
    _ -> U(e)

fun urPure(e: expr)
  e.urExpr.toExpr

fun toExpr(k: kexpr)
  match k
    U(org) -> org
    I(e') -> e'
    _ -> fail("core/unreturn urPure: should not happen: return inside pure expression")

alias alter<x> = (x -> ureff defGroup)
alias maybechanged = either<(alter<list<expr>>, list<kexpr>), (alter<expr>, kexpr)>

fun urLet(org: expr, defgroups: list<defGroup>, kbody: kexpr): ureff kexpr
  fun urLetDefGroup(dg: defGroup)
    match dg
      DefRec(dfs) ->
        val (mkDefs, kexprs) = dfs.map(urDef).unzip
        Left((fn(es) DefRec(mkDefs.zipwith(es, fn(make, d) make(d))), kexprs))
      DefNonRec(d) ->
        val (mkDef, kexpr) = d.urDef
        Right((fn(e) DefNonRec(mkDef(e)), kexpr))
  fun is-unchanged(e: maybechanged): bool
    match e
      Left((_, dgs)) -> dgs.all(is-u)
      Right((_, dg)) -> dg.is-u
  fun addDef(d: defGroup, e: expr): expr
    match e
      Let(defs, e') -> Let(Cons(d, defs), e')
      _ -> Let([d], e)
  fun fold(l: list<maybechanged>, kexpr: kexpr)
    match l
      Nil -> kexpr
      Cons(Left((mkDefGroup, kexprs)), kdefgs) -> 
        kdefgs.fold(Nothing.emapK(fn(e) addDef(mkDefGroup(kexprs.map(toExpr)), e), kexpr))
      Cons(Right((mkDefGroup, kdefexpr)), kdefgs) -> 
        fun combine(e1: expr, e2: expr)
          addDef(mkDefGroup(e1), e2)
        kdefgs.fold(Nothing.bind(combine, kdefexpr, kexpr))
  val kdefgs = defgroups.map(urLetDefGroup)
  if kdefgs.all(is-unchanged) then
    Just(org).emapK(fn(e) makeLet(defgroups, e), kbody)
  else kdefgs.reverse.fold(kbody)

fun urCase(org: expr, scruts: list<expr>, branches: list<branch>): <div,exn,uniquePhase,ur,comp-flags,corePhase> kexpr
  val (mkBranches, kexprss) = branches.map(urBranch).unzip
  val ks = kexprss.concat
  if ks.all(is-u) then U(org)
  elif ks.all(fn(k) k.is-u || k.is-i) then
    I(Case(scruts, kexprss.zipwith(mkBranches, fn(kexprs, mk) mk(kexprs.map(toExpr)))))
  elif ks.filter(fn(k) !k.is-r).length <= 1 then
    // Directly inline
    fun f(c)
      Case(scruts, kexprss.zipwith(mkBranches, fn(kexprs, mk) mk(kexprs.map(fn(k) applyK(c, k)))))
    F(f)
  else
    // generate a local continuation function
    val name = "cont".unique-name
    val pname = "x".unique-name
    val eff = currentEff.unjust
    val tp = org.type-of
    val parName = TName(pname, tp)
    val parVar = Var(parName, InfoNone)
    fun f(c)
      val lam = Lam([parName], eff, c(parVar))
      val defTp = lam.type-of
      val def = Def(name, defTp, lam, Private, DefFun([Own]), InlineAuto, range/null, "")
      val defVar = Var(TName(name, defTp), InfoNone)
      fun app(e)
        App(defVar, [e])
      Case(scruts, kexprss.zipwith(mkBranches, fn(kexprs, mk) mk(kexprs.map(fn(k) applyK(app, k)))))
    F(f)

fun urBranch(b: branch)
  val (mkGuards, kexprs) = b.guards.map(urGuard).unzip
  (fn(es) Branch(b.patterns, mkGuards.zipwith(es, fn(make, e) make(e))), kexprs)

fun urGuard(g: guard)
  val kexpr = g.body.urExpr
  (fn(e) Guard(g.test, e), kexpr)

fun applyK(c: expr -> ureff expr, k: kexpr): ureff expr
  match k
    U(e) -> c(e)
    I(e) -> c(e)
    R(e) -> e // If returning, the continuation is ignored
    F(f) -> f(c)

fun emapUnK(org: expr, g, k)
  match k
    U(_) -> U(org)
    I(e) -> I(g(e))
    R(r) -> I(g(r))
    F(f) -> I(g(f(fn(i) i)))

fun emapK(mbOrg: maybe<expr>, g, k)
  match k
    U(e) -> match mbOrg
      Nothing -> I(g(e))
      Just(org) -> U(org)
    I(e) -> I(g(e))
    R(r) -> R(g(r))
    F(f) -> F(fn(c) g(f(c)))

fun bind(mbOrg: maybe<expr>, combine, ke1, ke2)
  match (ke1, ke2)
    (R(r), _) -> R(r)
    (U(a), k) -> match k
      U(b) -> match mbOrg
        Nothing -> I(combine(a, b))
        Just(org) -> U(org)
      I(e) -> I(combine(a, e))
      R(r) -> R(combine(a, r))
      F(g) -> F(fn(c) combine(a, g(c)))
    (I(e1), k) -> match k
      U(b) -> I(combine(e1, b))
      I(e2) -> I(combine(e1, e2))
      R(r) -> R(combine(e1, r))
      F(g) -> F(fn(c) combine(e1, g(c)))
    (F(f), k) -> match k
      U(b) -> F(fn(c) f(fn(e) combine(e, c(b))))
      I(e) -> F(fn(c) f(fn(e1) combine(e1, c(e))))
      R(r) -> R(f(fn(e) combine(e, r)))
      F(g) -> F(fn(c) f(fn(e) combine(e, g(c))))



  



import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/failure
import compiler/platform/config
import compiler/common/range
import compiler/syntax/syntax
import compiler/common/syntax
import compiler/common/color-scheme
import std/data/linearmap
import compiler/lib/pprint

fun fixityResolve(fixMap: fixities, program: userProgram)
  val fixMap1 = fixitiesCompose(fixMap, program.fixDefs.extractFixMap)
  with handleFixities(fixMap1)
  val defs1 = program.defs.resolveDefs()
  program(defs=defs1)

fun extractFixMap(fds: list<fixDef>): fixities
  fun extractFix(FixDef(name, fixity): fixDef)
    (name, fixity)
  fixitiesNew(fds.map(extractFix))

// Rewrite syntax tree
fun resolveDefGroup(dg: defGroup<userType>)
  match dg
    DefRec(dfs) -> DefRec(dfs.map(resolve))
    DefNonRec(df) -> DefNonRec(resolve(df))

fun def/resolve(d: def<userType>)
  val binder' = d.binder.resolve
  d(binder=binder')

fun binder/resolve(b: valueBinder<t, a>, ?resolve: (a) -> fixEff a): fixEff valueBinder<t, a>
  val expr' = b.expr.resolve
  b(expr=expr')

fun list/resolve(ls: list<a>, ?resolve: (a) -> fixEff a): fixEff list<a>
  ls.map(resolve)

fun expr/resolve(ex: userExpr): fixEff userExpr
  match ex
    Lam(binds, expr, rng) ->
      val binds' = binds.resolve
      val expr' = expr.resolve
      Lam(binds', expr', rng)
    Let(defs, expr, rng) ->
      val defs' = defs.resolve
      val expr' = expr.resolve
      Let(defs', expr', rng)
    Bind(def, expr, rng) ->
      val def' = def.resolveDef
      val expr' = expr.resolve
      Bind(def', expr', rng)
    App(f, nargs, rng) ->
      val f' = f.resolve
      val nargs' = nargs.map(fn((n, e)) (n, e.resolve))
      if f.is-var then
        resolve(nargs'.map(snd))
      else  
        App(f', nargs', rng)
    Var -> ex
    Literal -> ex
    Ann(expr, ty, rng) ->
      val expr' = expr.resolve
      Ann(expr', ty, rng)
    Case(expr, brs, rng) ->
      val expr' = expr.resolve
      val brs' = brs.map(resolve)
      Case(expr', brs', rng)
    Parens(expr, nm, rng) ->
      val expr' = expr.resolve
      Parens(expr', nm, rng)
    Handler(shallow, scoped, over, allowMask, eff, pars, reinit, ret, finally, ops, hrng, rng) ->
      val ret' = ret.resolve
      val ops' = ops.map(resolve)
      val reinit' = reinit.resolve
      val final' = finally.resolve
      Handler(shallow, scoped, over, allowMask, eff, pars, reinit', ret', final', ops', hrng, rng)
    Inject(tp, expr, b, rng) ->
      val expr' = expr.resolve
      Inject(tp, expr', b, rng)

fun maybe/resolve(ex: maybe<a>, ?resolve: (a) -> fixEff a): fixEff maybe<a>
  ex.map(resolve)

fun branch/resolve(branch: branch<userType>)
  match branch
    Branch(patt, guards) -> Branch(patt, guards.map(resolve))

fun guard/resolve(g: guard<userType>)
  match g
    Guard(test, expr) -> Guard(test.resolve, expr.resolve)

fun handlerbranch/resolve(hb: handlerBranch<userType>)
  match hb
    HandlerBranch(branchExpr=e) -> hb(branchExpr=e.resolve)

// Fixity map for all operators
alias fixities = name-map<fixity>
val fixitiesEmpty: fixities = LinearMap([])

fun findFixity(fixities: fixities, name: name): fixity
  fixities.lookup(name).default(FixInfix(50, AssocNone))

fun fixitiesCompose(fix1: fixities, fix2: fixities): fixities
  fix2.list.foldl(fix1) fn(acc, (name, fixity))
    match fix1.lookup(name)
      Just(x as FixInfix) -> acc.add(name, x)
      _ -> acc.add(name, fixity)

fun fixitiesNew(fs: list<(name, fixity)>): fixities
  fixitiesEmpty + fs.filter(fn(f) f.snd.is-fixInfix)

effect fixityEff
  fun addFixError(s: doc, r: range): ()
  fun getFixities(): fixities
  fun updateFixities(f: fixities -> pure fixities): ()

alias fixEff = <fixityEff, pure, comp-flags>

fun handleFixities(initial: fixities, f: () -> <fixityEff,pure|e> a): <pure|e> (a, fixities, list<doc>)
  var fixes := initial
  var errors := []
  with handler
    fun getFixities()
      fixes
    fun updateFixities(f': fixities -> pure fixities)
      fixes := f'(fixes)
    fun addFixError(s, rng)
      errors := Cons(s, errors)
  (mask<local>{f()}, fixes, errors)

// Resolve fixities:
// The algorithm is written a bit long to enable easy extension to prefix, postfix, and distfix operators

value struct op { expr: userExpr; fixity: fixity }
value type term
  Term(expr: userExpr)
  Oper(op: op)

alias exprStack = list<userExpr>
alias opStack = list<op>

fun fixities-resolve(exprs: list<a>, ?resolve: (a) -> fixEff a): fixEff a
  val fixMap = getFixities()
  terms/resolve([], [], exprs.map(fn(e) e.toTerm(fixMap)))

// Find out if this is an operator
fun toTerm(expr: userExpr, fixities: fixities): term
  match expr
    Var(name, True) -> Oper(Op(expr, findFixity(fixities, name)))
    _ -> Term(expr)

// The real resolve algorithm uses Dijkstra's strategy with two stacks
fun terms/resolve(exprs: exprStack, os: opStack, tms: list<term>): fixEff userExpr
  match (exprs, os, tms)
    // final term computed
    ([x], [], []) -> x
    // cleanup stage, apply all ops
    (xs, ops as Cons, []) -> 
      apply(xs, ops, [])
    // always push terms
    (xs, ops, Cons(Term(t), tt)) ->
      resolve(Cons(t, xs), ops, tt)
    // prefix operator
    (xs, ops, Cons(Oper(t as Op(Var, FixPrefix)), tt)) ->
      push(xs, ops, tt, t)
    // postfix operator
    (xs, ops, Cons(Oper(t as Op(_, FixPostfix)), tt)) ->
      push(xs, ops, tt, t)
    // infix operator
    (xs, ops, ts as Cons(Oper(t as Op(_, FixInfix(_, assoc))), tt)) ->
      val prec = t.precedenceOp
      val precCtx =
        match ops
          Cons(o) -> o.precedenceOp
          _ -> 0
      if prec > precCtx then push(xs, ops, tt, t)
      elif prec < precCtx then apply(xs, ops, ts)
      else
        ops.checkAmbiguous(t)
        if assoc == AssocRight then push(xs, ops, tt, t) else apply(xs, ops, ts)
    ([], [], []) -> fail("static/fixity-resolve resolveTerms: no term: fix parser")
    _ -> fail("static/fixity-resolve resolveTerms: fixity resolver error")

fun precedenceOp(Op(_, fix): op)
  fix.precedence

fun precedence(f: fixity)
  match f
    FixInfix(p) -> p
    FixPrefix -> 102
    FixPostfix -> 101

fun checkAmbiguous(ops: opStack, Op(op, fix): op)
  match (ops, fix)
    (Cons(Op(_, fixCtx as FixInfix(_, assocCtx))), FixInfix(_, assoc)) | assoc.is-assocNone || !(assocCtx == assoc) ->
      ambiguous(fixCtx, fix, op)
    _ -> ()

fun ambiguous(fixCtx: fixity, fix: fixity, op: userExpr)
  val opText =
    match op
      Var(nm) -> nm.pretty |.| space
      _ -> empty
  val msg = "Ambiguous ".text |+| fix.ppFixity |+| "operator".text |+| opText |.| "in a".text |+| fixCtx.ppFixity |+| "context".text |-| " hint: add parenthesis around the sub-expression to disambiguate".text
  addFixError(msg, op.range)

fun ppFixity(f: fixity): doc
  match f
    FixInfix(_, assoc) ->
      match assoc
        AssocLeft -> "left-associative".text
        AssocRight -> "right-associative".text
        AssocNone -> "non-associative".text
    FixPrefix -> "prefix".text
    FixPostfix -> "postfix".text

// Helper operations: push and apply
fun push(xs: exprStack, ops: opStack, ts: list<term>, t: op): fixEff userExpr 
  resolve(xs, Cons(t, ops), ts)

fun apply(xs: list<expr<userType>>, ops: list<op>, ts: list<term>)
  match ops
    Cons(Op(op, FixPostfix), rst) ->
      val ys = applyUnaryOp(op, xs)
      resolve(ys, rst, ts)
    Cons(Op(op, FixPrefix), rst) ->
      val ys = applyUnaryOp(op, xs)
      resolve(ys, rst, ts)
    Cons(Op(op, FixInfix(_, _)), rst) ->
      val ys = applyInfixOp(op, xs)
      resolve(ys, rst, ts)
    _ -> fail("static/fixity-resolve apply: fixity resolver error")

fun applyUnaryOp(op: expr<t>, ts: list<expr<t>>): fixEff list<expr<t>>
  match ts
    Cons(t, ts) -> Cons(App(op, [(Nothing, t)], t.range.combine(op.range)), ts)
    _ -> 
      addFixError("Unary operator has not enough arguments".text, op.range )
      ts

fun applyInfixOp(op: expr<t>, ts: list<expr<t>>): fixEff list<expr<t>>
  match ts
    Cons(t1, Cons(t2, ts)) -> Cons(App(op, [(Nothing, t1), (Nothing, t2)], t1.range.combine(t2.range)), ts)
    _ -> 
      addFixError("Infix operator has not enough arguments".text, op.range)
      ts

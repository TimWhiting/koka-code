import compiler/core/core
import compiler/type/type
import compiler/common/name

fun unrollDefs(unrollMax: int)
  setCoreDefs(unrollDefGroups(getCoreDefs()))

fun unrollDefGroups(defGroups: list<defGroup>)
  defGroups.map(unrollDefGroup).concat

fun unrollDefGroup(defGroup: defGroup)
  match defGroup
    DefRec([d]) -> d.unrollRecDef
    _ -> [defGroup]

fun unrollRecDef(d: def)
  val dgs = match d.defExpr
    Lam(pars, eff, body) -> unrollBody(d, [], pars, eff, body)
    TypeLam(tpars, Lam(pars, eff, body)) -> unrollBody(d, tpars, pars, eff, body)
    _ -> []
  if dgs.is-nil then DefRec([d]) else dgs

fun unrollBody(d: def, tpars: list<typeVar>, pars: list<tName>, eff: keffect, body: expr)
  match body
    Case(exprs, branches as Cons(Branch(pats))) | exprs.all(fn(x) x.cost == 0)
      match branches.extractNonRecBranches(d.defName, [])
        (nonrecbs, recbs) | nonrecbs.length > 0 && recbs.length > 0 ->
          val dname = d.defName
          val rname = dname.uniqueTNameFrom
          val info = InfoArity(tpars.length, pars.length)
          val sub = [(dname, Var(rname, info))]
          val rdef = d(defName=rname.getName, defExpr=(sub |-> d.defExpr), vis=Private)
          val rcall = App(TypeApp(Var(rname, info), tpars.map(fn(tv) TVar(tv)), pars.map(fn(v) Var(v, InfoNone))))
          val wild = Branch(pats.map(fn(_) PatWild), [Guard(exprTrue, rcall)])
          fun mkFun(b)
            val l = Lam(pars, eff, b)
            if tpars.is-nil then l else fn(e) TypeLam(tpars, tpars, l)
          val ddef = d(defExpr=mkFun(Case(exprs, nonrecbs ++ [wild])), inl=InlineAlwyas,
            doc="// unrolling of singleton matches of " ++ rname.getName.show ++ "\n")
          // TODO: Verbose doc
          [DefRec([rdef]), DefNonRec(ddef)]
        _ -> []
    -> [] // TODO: small let bindings?

fun extractNonRecBranches(dname: tName, recs: list<branch>, bs: list<branch>): (list<branch>, list<branch>)
  match bs
    // Stop on end
    Nil -> (Nil, recs)
    // stop also when we cannot push down patterns of recursive branches any further
    Cons(b, bs') | recs.any(fn(r) r.matchCanOverlap(b)) ->
      (Nil, recs ++ [b] ++ bs)
    // otherwise
    Cons(b as Branch(pats, guards)) ->
      // we only want cheap matches in the unrolling, and they should be non-recursive    
      if pats.any(fn(p) !p.singletonPat) || guards.freeVars.mamber(defname) then
        // assume it contains a recursive call
        // push down as long the other patterns don't match to maximize non-recursive matches
        extractNonRecBranches(dname, (recs ++ [b]), bs')
      else
        // surely non-recursive, keep going
        val (bs1, bs2) = extractNonRecBranches(dname, recs, bs')
        val newb = if recs.is-nil then b else b.dontSkip
        (Cons(newb, bs1), bs2)

// is this a singleton (which can be matched without memory access)
fun singletonPat(p: pattern): bool
  match p
    PatVar(_, p') -> p'.singletonPat
    PatCon(_, []) -> True
    PatWild -> True
    PatLit -> True
    _ -> False

// Patterns could overlap? (can be conservative, returning True is always ok)
fun matchCanOverlap(Branch(pats1, _): branch, Branch(pats2, _): branch)
  fun patCanOverlap(pp: (pattern, pattern))
    match pp
      (PatWild, _) -> True
      (_, PatWild) -> True
      (PatVar(_, p1), p2) -> patCanOverlap((p1, p2))
      (p1, PatVar(_, p2)) -> patCanOverlap((p1, p2))
      (PatLit(lit1), PatLit(lit2)) -> lit1 == lit2
      (PatCon(name1), PatCon(name2)) -> name1 == name2 // TODO: make more precise
      _ -> True
  pats1.zip(pats2).any(patCanOverlap)

fun dontSkip(Branch(pats, guards): branch)
  fun noSkip(pat: pattern)
    match pat
      PatVar(name, p) -> PatVar(name, p.noSkip)
      PatCon(patName, ps, repr, typeArgs, kexists, typeRes, info, _) ->
        PatCon(patName, ps.map(noSkip), repr, typeArgs, kexists, typeRes, info, False)
      _ -> pat 
  Branch(pats.map(noSkip), guards)





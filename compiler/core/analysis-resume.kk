import compiler/common/name
import compiler/common/name-prim
import compiler/common/resume-kind
import compiler/core/core
import compiler/core/corevar
import std/data/linearset

fun analyze(defNm: name, opNm: name, isRaw: bool, e: expr)
  match e
    Lam(_, _, body) -> if !isRaw then body.tail-expr else ResumeNormalRaw
    TypeLam(_, body) -> body.analyze(defNm, opNm, isRaw)
    TypeApp(body) -> body.analyze(defNm, opNm, isRaw)
    App(_, [body]) -> body.analyze(defNm, opNm, isRaw)
    _ -> fail("core/analysis-resume, invalid branch expression")

fun tail-expr(e: expr)
  e.expr'(ResumeTail)

fun expr(e: expr)
  e.expr'(ResumeScopedOnce)

fun is-resuming-elem(s: linearSet<tName>)
  s.member(resumeName) || s.member(finalizeName) || s.member(resumeShallowName)

fun tname/is-resuming(t: tName)
  t == resumeName || t == finalizeName || t == resumeShallowName

fun name/is-resuming(t: name)
  t == resumeName.getName || t == resumeShallowName.getName

fun expr'(e: expr, defaultKind: resumeKind): resumeKind
  match e
    Lam -> if e.freeVars.is-resuming-elem then ResumeNormal else ResumeNever
    App(Var(tname), args) | tname.is-resuming ->
      defaultKind && args.exprsAnd && (if tname == resumeShallowName then ResumeOnce else ResumeNever)
    App(f, args) -> Cons(f, args).exprsAnd
    TypeLam(_, body) -> body.expr'(defaultKind)
    TypeApp(body) -> body.expr'(defaultKind)
    Var(tname) -> if tname.is-resuming then ResumeNormal else ResumeNever
    Con -> ResumeNever
    Lit -> ResumeNever
    Let([DefNonRec(d)], e') | d.getName.is-resuming -> e'.expr'(defaultKind)
    Let(dgs, bd) -> 
      if dgs.flatten().map(fn(d) d.boundVars + d.freeVars).unions.is-resuming then ResumeNormal else bd.expr'(defaultKind)
    Case(exprs, brnchs) ->
      exprs.exprsAnd && branches.branches(defaultKind)

fun branches(bs: list<branch>, defaultKind: resumeKind): resumeKind
  bs.map(fn(b) b.branch(defaultKind)).ors

fun branch(b: branch, defaultKind: resumeKind): resumeKind
  b.guards.map(fn(g) g.guard(defaultKind)).ors

fun guard(g: guard, defaultKind: resumeKind): resumeKind
  g.body.expr && g.test.expr'(defaultKind)

fun ands(exprs: list<resumeKind>)
  exprs.foldl(ResumeNever, fn(e, e') e && e')

fun ors(exprs: list<resumeKind>)
  exprs.foldl(ResumeNever, fn(e, e') e || e')

fun is-scoped(rk: resumeKind): bool
  match rk
    ResumeNormal -> False
    ResumeOnce -> False
    _ -> True

fun (&&)(rk1: resumeKind, rk2: resumeKind): resumeKind
  match (rk1, rk2)
    (ResumeNever, rk) -> rk
    (rk, ResumeNever) -> rk
    _ -> if rk1.is-scoped && rk2.is-scoped then ResumeScoped else ResumeNormal

fun (||)(rk1: resumeKind, rk2: resumeKind): resumeKind
  match (rk1, rk2)
    (ResumeOnce, rk) | rk.index >= ResumeScoped.index -> ResumeNormal
    (rk, ResumeOnce) | rk.index >= ResumeScoped.index -> ResumeNormal
    _ -> if  rk1.index >= rk2.index then rk1 else rk2  
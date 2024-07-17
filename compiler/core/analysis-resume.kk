import compiler/common/name
import compiler/common/name-prim
import compiler/common/resume-kind
import compiler/core/core
import compiler/core/corevar
import compiler/type/type
import std/data/linearset
import compiler/common/failure

fun analyze(defNm: name, opNm: name, isRaw: bool, e: expr)
  match e
    Lam(_, _, body) -> if !isRaw then body.tail-expr else ResumeNormalRaw
    TypeLam(_, body) -> analyze(defNm, opNm, isRaw, body)
    TypeApp(body) -> analyze(defNm, opNm, isRaw, body)
    App(_, [body]) -> analyze(defNm, opNm, isRaw, body)
    _ -> fail("core/analysis-resume, invalid branch expression")

fun tail-expr(e: expr)
  e.expr'(ResumeTail)

fun expr(e: expr)
  e.expr'(ResumeScopedOnce)

val resumeName = TName(new-name("resume"), typeVoid)
val resumeShallowName = TName(new-name("resume-shallow"), typeVoid)
val finalizeName = TName(new-name("finalize"), typeVoid)

fun is-resuming-elem(s: linearSet<tName>)
  s.member(resumeName) || s.member(finalizeName) || s.member(resumeShallowName)

fun tname/is-resuming(t: tName)
  t == resumeName || t == finalizeName || t == resumeShallowName

fun name/is-resuming(t: name)
  t == resumeName.get-name || t == resumeShallowName.get-name

fun expr'(e: expr, defaultKind: resumeKind): div resumeKind
  match e
    Lam -> if e.free-vars.is-resuming-elem then ResumeNormal else ResumeNever
    App(Var(tname), args) | tname.is-resuming ->
      defaultKind && args.map(expr).ands && (if tname == resumeShallowName then ResumeOnce else ResumeNever)
    App(f, args) -> Cons(f, args).map(expr).ands
    TypeLam(_, body) -> body.expr'(defaultKind)
    TypeApp(body) -> body.expr'(defaultKind)
    Var(tname) -> if tname.is-resuming then ResumeNormal else ResumeNever
    Con -> ResumeNever
    ELit -> ResumeNever
    Let([DefNonRec(d)], e') | d.def-name.is-resuming -> e'.expr'(defaultKind)
    Let(dgs, bd) -> 
      if dgs.flatten().map(fn(d) d.bound-vars + d.free-vars).unions.is-resuming-elem then ResumeNormal else bd.expr'(defaultKind)
    Case(exprs, brnchs) ->
      exprs.map(expr).ands && brnchs.branches(defaultKind)

fun branches(bs: list<branch>, defaultKind: resumeKind): div resumeKind
  bs.map(fn(b) b.branch(defaultKind)).ors

fun branch(b: branch, defaultKind: resumeKind): div resumeKind
  b.guards.map(fn(g) g.guard(defaultKind)).ors

fun guard(g: guard, defaultKind: resumeKind): div resumeKind
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
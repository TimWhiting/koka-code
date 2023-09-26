import compiler/common/name
import compiler/common/name-prim
import compiler/common/resume-kind
import compiler/core/core
import compiler/core/corevar
import newstd/data/linearset

fun analyzeResume(defNm: name, opNm: name, isRaw: bool, e: expr)
  match e
    Lam(_, _, body) -> if !isRaw then body.arTailExpr else ResumeNormalRaw
    TypeLam(_, body) -> body.analyzeResume(defNm, opNm, isRaw)
    TypeApp(body) -> body.analyzeResume(defNm, opNm, isRaw)
    App(_, [body]) -> body.analyzeResume(defNm, opNm, isRaw)
    _ -> fail("core/analysis-resume, invalid branch expression")

fun arTailExpr(e: expr)
  e.arExpr'(ResumeTail)

fun arExpr(e: expr)
  e.arExpr'(ResumeScopedOnce)

fun isResumingElem(s: linearSet<tName>)
  s.member(resumeName) || s.member(finalizeName) || s.member(resumeShallowName)

fun isResuming(t: tName)
  t == resumeName || t == finalizeName || t == resumeShallowName

fun isResuming(t: name)
  t == resumeName.getName || t == resumeShallowName.getName

fun arExpr'(e: expr, defaultKind: resumeKind): resumeKind
  match e
    Lam -> if e.freeVars.isResumingElem then ResumeNormal else ResumeNever
    App(Var(tname), args) | tname.isResuming ->
      defaultKind && args.arExprsAnd && (if tname == resumeShallowName then ResumeOnce else ResumeNever)
    App(f, args) -> Cons(f, args).arExprsAnd
    TypeLam(_, body) -> body.arExpr'(defaultKind)
    TypeApp(body) -> body.arExpr'(defaultKind)
    Var(tname) -> if tname.isResuming then ResumeNormal else ResumeNever
    Con -> ResumeNever
    Lit -> ResumeNever
    Let([DefNonRec(d)], e') | d.getName.isResuming -> e'.arExpr'(defaultKind)
    Let(dgs, bd) -> 
      if dgs.flatten().map(fn(d) d.boundVars + d.freeVars).unions.isResuming then ResumeNormal else bd.arExpr'(defaultKind)
    Case(exprs, brnchs) ->
      exprs.arExprsAnd && branches.arBranches(defaultKind)

fun arBranches(bs: list<branch>, defaultKind: resumeKind): resumeKind
  bs.map(fn(b) b.arBranch(defaultKind)).ors

fun arBranch(b: branch, defaultKind: resumeKind): resumeKind
  b.guards.map(fn(g) g.arGuard(defaultKind)).ors

fun arGuard(g: guard, defaultKind: resumeKind): resumeKind
  g.body.arExpr && g.test.arExpr'(defaultKind)

fun ands(exprs: list<resumeKind>)
  exprs.foldl(ResumeNever, fn(e, e') e && e')

fun ors(exprs: list<resumeKind>)
  exprs.foldl(ResumeNever, fn(e, e') e || e')

fun isScoped(rk: resumeKind): bool
  match rk
    ResumeNormal -> False
    ResumeOnce -> False
    _ -> True

fun (&&)(rk1: resumeKind, rk2: resumeKind): resumeKind
  match (rk1, rk2)
    (ResumeNever, rk) -> rk
    (rk, ResumeNever) -> rk
    _ -> if rk1.isScoped && rk2.isScoped then ResumeScoped else ResumeNormal

fun (||)(rk1: resumeKind, rk2: resumeKind): resumeKind
  match (rk1, rk2)
    (ResumeOnce, rk) | rk.index >= ResumeScoped.index -> ResumeNormal
    (rk, ResumeOnce) | rk.index >= ResumeScoped.index -> ResumeNormal
    _ -> if  rk1.index >= rk2.index then rk1 else rk2  
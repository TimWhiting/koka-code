import sexpr
import newstd/data/linearset

type program
  Program(defs: list<def>, free: vars = defs.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())

pub alias vars = linearSet<sexpr, <>>

val globalLabel = unsafe-total{ref(0)}
fun getLabel(): int
  unsafe-total
    val l = !globalLabel
    globalLabel.set(l + 1)
    l
val sExprEq = analysis/cps/sexpr/(==)
val noFreeVars = linearSet([], sExprEq)

type def
  DefImplicit(value: exp, free: vars = value.free, label:int=getLabel())
  DefVar(name: sexpr, value: exp, free: vars = value.free - name, label:int=getLabel())
  DefFun(name: sexpr, formals: formals, body: body, free: vars = body.free - formals - name, label:int=getLabel())

alias binding = (sexpr, exp)
alias formals = (list<sexpr>, maybe<sexpr>)

pub fun free(b: binding): vars
  b.snd.free - b.fst

pub fun (-)(l: vars, v: formals): e vars
  l - v.fst - v.snd

type body
  Body(defs: list<def>, exps: list<exp>, free: vars = defs.map(free).foldl(exps.map(free).foldl(noFreeVars, fn(a, b) a + b), fn(a, b) a + b), label:int=getLabel())

type clause
  SelfClause(test: exp, free: vars = test.free, label:int=getLabel())
  TestClause(test: exp, exps: list<exp>, free: vars = test.free + exps.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  ProcClause(test: exp, proc: exp, free: vars = test.free + proc.free, label:int=getLabel())
  ElseClause(exps: list<exp>, free: vars = exps.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())

type exp
  SelfLit(lit: sexpr, free: vars = noFreeVars, label:int=getLabel())
  QuoteLit(lit: sexpr, free: vars = noFreeVars, label:int=getLabel())
  Ref(name: sexpr, free: vars = linearSet([name], sExprEq), label:int=getLabel())
  App(f: exp, args: list<exp>, free: vars = f.free + args.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  KLambda(formals: (list<sexpr>, maybe<sexpr>), body: body, free: vars = body.free - formals, label:int=getLabel())
  ULambda(formals: (list<sexpr>, maybe<sexpr>), body: body, free: vars = body.free - formals, label:int=getLabel())
  Lambda(formals: (list<sexpr>, maybe<sexpr>), body: body, free: vars = body.free - formals, label:int=getLabel())
  IfE(test: exp, ifTrue: exp, ifFalse: maybe<exp>, free: vars = test.free + ifTrue.free + ifFalse.map(free).default(noFreeVars), label:int=getLabel())
  SetE(name: sexpr, value: exp, free: vars = linearSet([name], sExprEq) + value.free, label:int=getLabel())
  Values(vals: list<exp>, free: vars = vals.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  LetValues(bindings: list<(sexpr, exp)>, body: body, free: vars = body.free + bindings.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  Begin(body: body, free: vars = body.free, label:int=getLabel())
  And(exps: list<exp>, free: vars = exps.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  Or(exps: list<exp>, free: vars = exps.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  Cond(clauses: list<clause>, free: vars = clauses.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  Undefined(free:vars=noFreeVars, label:int=getLabel())
  Void(free:vars=noFreeVars, label:int=getLabel())
  Let(bindings: list<(sexpr, exp)>, body: body, free: vars = body.free + bindings.map(free).foldl(noFreeVars, fn(a, b) a + b), label:int=getLabel())
  // TODO Free for this is a bit more subtle
  LetStar(bindings: list<(sexpr, exp)>, body: body, free: vars = body.free + bindings.map(free).foldl(noFreeVars, fn(a, b) a + b) - bindings.map(fst), label:int=getLabel()) 
  LetRec(bindings: list<(sexpr, exp)>, body: body, free: vars = body.free + bindings.map(free).foldl(noFreeVars, fn(a, b) a + b) - bindings.map(fst), label:int=getLabel())

fun asBody(e: exp): body
  match e
    Begin(b as Body([], [_])) -> b
    _ -> Body([], [e]) 

fun consExp(car: exp, cdr: exp): exp
  App(Ref(sCons), [car, cdr])

fun listExp(es: list<exp>)
  match es
    [] -> QuoteLit(SNil())
    Cons(hd, tail) -> consExp(hd, listExp(tail))

fun seq(fst: exp, snd: exp): exp
  Begin(Body([], [fst, snd]))

fun lit(e: exp): exn sexpr
  match e
    SelfLit(lit) -> lit
    QuoteLit(lit) -> lit
    _ -> throw("not a literal")

fun formals(e: exp): exn formals
  match e
    KLambda(formals) -> formals
    ULambda(formals) -> formals
    Lambda(formals) -> formals
    _ -> throw("not a lambda")

fun body(e: exp): exn body
  match e
    KLambda(_, body) -> body
    ULambda(_, body) -> body
    Lambda(_, body) -> body
    _ -> throw("not a lambda")

fun expansion(e: sexpr): exp
  match e
    SCons(car, cdr) -> consExp(car.expansion, cdr.expansion)
    _ -> QuoteLit(e)

fun show(p: program): div string
  p.defs.map(fn(d) d.show).join("\n")

fun show(d: def): div string
  match d
    DefImplicit(value) ->
      value.show
    DefVar(name, value) ->
      "(define " ++ name.show ++ " " ++ value.show ++ ")"
    DefFun(name, formals, body) ->
      "(define (" ++ name.show ++ " " ++ formals.show ++ ") " ++ body.show ++ ")"

fun show(b: body): div string
  match b
    Body(defs, exps) ->
      defs.map(fn(d) d.show).join("\n") ++ "\n" ++ exps.map(fn(e) e.show).join("\n")

fun show(f: formals): div string
  match f
    (formals, ms) ->
      "(" ++ formals.map(show).join(" ") ++ ms.map(fn(m) " . " ++ m.show).default("") ++ ")"

fun show(b: binding): div string
  match b
    (name, value) ->
      "(" ++ name.show ++ " " ++ value.show ++ ")"

fun show(c: clause): div string
  match c
    SelfClause(test) ->
      test.show
    TestClause(test, exps) ->
      "(" ++ test.show ++ " => " ++ exps.map(show).join(" ") ++ ")"
    ProcClause(test, proc) ->
      "(" ++ test.show ++ " " ++ proc.show ++ ")"
    ElseClause(exps) ->
      "(else " ++ exps.map(show).join(" ") ++ ")"

fun show(e: exp): div string
  match e
    SelfLit(lit) ->
      lit.show
    QuoteLit(lit) ->
      "'" ++ lit.show
    Ref(name) ->
      name.show
    App(f, args) ->
      "(" ++ f.show ++ " " ++ args.map(show).join(" ") ++ ")"
    KLambda(formals, body) ->
      "(lambda " ++ formals.show ++ " " ++ body.show ++ ")"
    ULambda(formals, body) ->
      "(λ " ++ formals.show ++ " " ++ body.show ++ ")"
    Lambda(formals, body) ->
      "(lambda " ++ formals.show ++ " " ++ body.show ++ ")"
    IfE(test, ifTrue, ifFalse) ->
      "(if " ++ test.show ++ " " ++ ifTrue.show ++ " " ++ ifFalse.map(show).default("") ++ ")"
    SetE(name, value) ->
      "(set! " ++ name.show ++ " " ++ value.show ++ ")"
    Values(vals) ->
      "(values " ++ vals.map(show).join(" ") ++ ")"
    LetValues(bindings, body) ->
      "(let-values (" ++ bindings.show-list(fn(x) x.show) ++ ") " ++ body.show ++ ")"
    Begin(body) ->
      "(begin " ++ body.show ++ ")"
    And(exps) ->
      "(and " ++ exps.map(show).join(" ") ++ ")"
    Or(exps) ->
      "(or " ++ exps.map(show).join(" ") ++ ")"
    Cond(clauses) ->
      "(cond " ++ clauses.map(show).join(" ") ++ ")"
    Undefined ->
      "#undefined"
    Void ->
      "#void"
    Let(bindings, body) ->
      "(let (" ++ bindings.map(show).join(" ") ++ ") " ++ body.show ++ ")"
    LetStar(bindings, body) ->
      "(let* (" ++ bindings.map(show).join(" ") ++ ") " ++ body.show ++ ")"
    LetRec(bindings, body) ->
      "(letrec (" ++ bindings.map(show).join(" ") ++ ") " ++ body.show ++ ")"
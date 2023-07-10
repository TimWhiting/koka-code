import sexpr
import newstd/data/linearset

type program
  Program(defs: list<def>)
  
type def
  DefImplicit(value: exp)
  DefVar(name: sexpr, value: exp)
  DefFun(name: sexpr, formals: formals, body: body)

alias binding = (sexpr, exp)
alias formals = (list<sexpr>, maybe<sexpr>)

type body
  Body(defs: list<def>, exps: list<exp>)

type clause
  SelfClause(test: exp)
  TestClause(test: exp, exps: list<exp>)
  ProcClause(test: exp, proc: exp)
  ElseClause(exps: list<exp>)

type exp
  SelfLit(lit: sexpr)
  QuoteLit(lit: sexpr)
  Ref(name: sexpr)
  App(f: exp, args: list<exp>)
  KLambda(formals: (list<sexpr>, maybe<sexpr>), body: body)
  ULambda(formals: (list<sexpr>, maybe<sexpr>), body: body)
  Lambda(formals: (list<sexpr>, maybe<sexpr>), body: body)
  IfE(test: exp, ifTrue: exp, ifFalse: maybe<exp>)
  SetE(name: sexpr, value: exp)
  Values(vals: list<exp>)
  LetValues(bindings: list<(sexpr, exp)>, body: body)
  Begin(body: body)
  And(exps: list<exp>)
  Or(exps: list<exp>)
  Cond(clauses: list<clause>)
  Undefined
  Void
  Let(bindings: list<(sexpr, exp)>, body: body)
  LetStar(bindings: list<(sexpr, exp)>, body: body)
  LetRec(bindings: list<(sexpr, exp)>, body: body)

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

alias vars = linearSet<sexpr, pure>

val sExprEq = analysis/cps/sexpr/(==)
val noFreeVars = linearSet([], sExprEq)
fun free(e: exp): pure vars
  match e
    SelfLit() -> noFreeVars
    QuoteLit() -> noFreeVars
    Undefined() -> noFreeVars
    Void() -> noFreeVars
    Ref(name) -> linearSet([name], (==))
    App(f, args) -> free(f) + args.map(free).foldl(noFreeVars, fn(a:vars, b:vars) a + b)
    KLambda(formals, body) -> free(body) - formals.fst
    ULambda(formals, body) -> free(body) - formals.fst
    Lambda(formals, body) -> free(body) - formals.fst
    IfE(test, ifTrue, ifFalse) -> free(test) + free(ifTrue) + ifFalse.map(free).default(noFreeVars)
    SetE(name, value) -> linearSet([name], sExprEq) + free(value)
    Values(vals) -> vals.map(free).foldl(noFreeVars, fn(a, b) a + b)
    LetValues(bindings, body) -> free(body) + bindings.map(fn(b) free(b.snd)).foldl(noFreeVars, fn(a, b) a + b)
    Begin(body) -> free(body)
    And(exps) -> exps.map(free).foldl(noFreeVars, fn(a, b) a + b)
    Or(exps) -> exps.map(free).foldl(noFreeVars, fn(a, b) a + b)
    Cond(clauses) -> clauses.map(free).foldl(noFreeVars, fn(a, b) a + b)
    Let(bindings, body) -> free(body) + bindings.map(fn(b) free(b.snd)).foldl(noFreeVars, fn(a, b) a + b)
    LetStar(bindings, body) -> free(body) + bindings.map(fn(b) free(b.snd)).foldl(noFreeVars, fn(a, b) a + b)
    LetRec(bindings, body) -> free(body) + bindings.map(fn(b) free(b.snd)).foldl(noFreeVars, fn(a, b) a + b)

fun free(c: clause): pure vars
  match c
    SelfClause(test) -> free(test)
    TestClause(test, exps) -> free(test) + exps.map(free).foldl(noFreeVars, fn(a, b) a + b)
    ProcClause(test, proc) -> free(test) + free(proc)
    ElseClause(exps) -> exps.map(free).foldl(noFreeVars, fn(a, b) a + b)

fun free(d: def): pure vars
  match d
    DefImplicit(value) -> free(value)
    DefVar(name, value) -> free(value) - name
    DefFun(name, formals, body) -> free(body) - formals.fst - name

fun free(bd: body): pure vars
  match bd
    Body(defs, exps) -> defs.map(free).foldl(exps.map(free).foldl(noFreeVars, fn(a, b) a + b), fn(a1, b1) a1 + b1)

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
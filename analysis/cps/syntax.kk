import parse
import std/os/path
import std/os/file
import std/os/dir

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

alias binding = (sexpr, exp)
alias formals = (list<sexpr>, maybe<sexpr>)

type body
  Body(defs: list<def>, exps: list<exp>)

type def
  ImplicitDef(value: exp)
  VariableDef(name: sexpr, value: exp)
  FunctionDef(name: sexpr, formals: formals, body: body)

type clause
  SelfClause(test: exp)
  TestClause(test: exp, exps: list<exp>)
  ProcClause(test: exp, proc: exp)
  ElseClause(exps: list<exp>)

type program
  Program(defs: list<def>)

fun expansion(e: sexpr): exp
  match e
    SCons(car, cdr) -> consExp(car.expansion, cdr.expansion)
    _ -> QuoteLit(e)

fun consExp(car: exp, cdr: exp): exp
  App(Ref(sCons), [car, cdr])

fun parseProgram(s: list<sexpr>): pure program
  Program(s.map(fn(e) e.parseDef))

fun parseOptionalExpr(s: list<sexpr>): pure maybe<exp>
  match s
    [] -> Nothing
    [e] -> Just(e.parseExpr)

fun parseExpr(e: sexpr): pure exp
  // trace("parseExpr: " ++ e.show)
  match e
    SNumber() -> SelfLit(e)
    SBool() -> SelfLit(e)
    SChar() -> SelfLit(e)
    SString() -> SelfLit(e)
    SName() -> Ref(e)
    ex -> 
      match ex.toList
        [SName("quote"), l] -> l.expansion
        [SName("quasiquote"), l] -> l.parseQuasiquote
        Cons(SName("lambda"), Cons(formals, body)) -> Lambda(formals.parseFormals, body.parseBody)
        Cons(SName("λ"), Cons(formals, body)) -> Lambda(formals.parseFormals, body.parseBody)
        Cons(SName("let"), Cons(bindings, body)) -> 
          match bindings
            name as SName() ->
              match body
                Cons(binds, realBody) ->
                  val bds = binds.parseBindings
                  val lam = Lambda((bds.map(fst), Nothing), realBody.parseBody)
                  LetRec([(name, lam)], Body([], [App(Ref(name), bds.map(snd))]))
            _ -> Let(bindings.parseBindings, body.parseBody)
        Cons(SName("let*"), Cons(bindings, body)) -> LetStar(bindings.parseBindings, body.parseBody)
        Cons(SName("letrec"), Cons(bindings, body)) -> LetRec(bindings.parseBindings, body.parseBody)
        [SName("set!"), s, exp] -> SetE(s, exp.parseExpr)
        Cons(SName("begin"), body) -> Begin(body.parseBody)
        Cons(SName("if-zero"), Cons(test, Cons(ifTrue, ifFalse))) -> IfE(App(Ref(SName("eq?")), [test.parseExpr]), ifTrue.parseExpr, ifFalse.parseOptionalExpr)
        Cons(SName("if"), Cons(test, Cons(ifTrue, ifFalse))) -> IfE(test.parseExpr, ifTrue.parseExpr, ifFalse.parseOptionalExpr)
        Cons(SName("or"), exps) -> Or(exps.map(parseExpr))
        Cons(SName("and"), exps) -> And(exps.map(parseExpr))
        Cons(c, s) -> App(c.parseExpr, s.map(parseExpr))
        _ -> SelfLit(e)

fun parseBindings(bds: sexpr): pure list<binding>
  // trace("Bindings " ++ bds.show)
  bds.toList.map(fn(b) b.parseBinding)

fun parseBinding(s: sexpr): pure binding
  match s
    SCons(name, SCons(exp, SNil())) -> (name, exp.parseExpr)
    _ -> throw("Binding with no expression " ++ s.show)


fun listExp(es: list<exp>)
  match es
    [] -> QuoteLit(SNil())
    Cons(hd, tail) -> consExp(hd, listExp(tail))

fun parseQuasiquote(e: sexpr, depth:int=1)
  // trace("QQ " ++ e.show)
  val l = (fn() e.toList).try.maybe
  match l
    Just([SName("unquote"), s]) -> if depth == 1 then parseExpr(s) else listExp([QuoteLit(SName("unquote")), s.parseQuasiquote(depth - 1)])
    Just([SName("quasiquote"), s]) -> listExp([QuoteLit(SName("quasiquote")), s.parseQuasiquote(depth + 1)])
    _ -> match e
      SCons(SCons(c as SName("unquote-splicing"), SCons(exp, SNil())), tl) -> 
        if depth == 1 then App(Ref(sAppend), [exp.parseExpr, tl.parseQuasiquote(depth)]) 
        else consExp(listExp([QuoteLit(c), exp.parseQuasiquote(depth - 1)]), tl.parseQuasiquote(depth))
      SCons(s, tl) -> consExp(s.parseQuasiquote(depth), tl.parseQuasiquote(depth))
      _ -> QuoteLit(e)
    

fun parseDef(e: sexpr): pure def
  // trace("Def " ++ e.show)
  match e
    SCons(SName("define"), SCons(SName(name), value)) ->
      VariableDef(SName(name), value.parseExpr)
    SCons(SName("define"), SCons(SCons(SName(name), formals), body)) ->
      FunctionDef(SName(name), formals.parseFormals, body.toList.parseBody)
    _ ->
      ImplicitDef(e.parseExpr)

fun parseFormals(s: sexpr): pure formals
  // trace("Formals")
  if s.isList then
    (s.toList, Nothing)
  else
    match s
      SCons() ->
        val (x, r) = s.toDottedList
        (x, Just(r))
      SName() -> ([], Just(s))

fun parseBody(l: list<sexpr>): pure body
  var defs := []
  var exps := []
  l.foreach fn(s)
    match s
      SCons(SName("define"), v) ->
        defs := Cons(v.parseDef, defs)
      _ ->
        exps := Cons(s.parseExpr, exps)
  Body(defs.reverse, exps.reverse)

fun show(p: program): div string
  p.defs.map(fn(d) d.show).join("\n")

fun show(d: def): div string
  match d
    ImplicitDef(value) ->
      value.show
    VariableDef(name, value) ->
      "(define " ++ name.show ++ " " ++ value.show ++ ")"
    FunctionDef(name, formals, body) ->
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

fun main()
  try({
    list-directory-recursive("/Users/timwhiting/koka_code/higher-order-programs/scheme".path).foreach fn(p)
      if is-file(p) then // nbody
        val fName = p.string
        if fName.ends-with(".scm").is-just then
          println(fName)
          if fName.ends-with("nbody.scm").is-just || fName.ends-with("nucleic-2.scm").is-just then
            ()
          else // if p.string.ends-with("scheme-to-c.scm").is-just then
            val s = parseFile(fName) // p.string)
            val pr = parseProgram(s)
            ()
          // else
          //   () // println(pr.show)
    },fn(e) {println("Error " ++ e.show)})
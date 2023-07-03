import parse

val sQuote = SName("quote")
val sQuasiquote = SName("quasiquote")
val sUnquote = SName("unquote")
val sUnquoteSplicing = SName("unquote-splicing")
val sCons = SName("cons")
val sList = SName("list")
val sAppend = SName("append")
val sDefine = SName("define")
val sLambda = SName("lambda")
val sLambday = SName("λ")
val sLet = SName("let")
val sLetStar = SName("let*")
val sLetRec = SName("letrec")
val sSetBang = SName("set!")
val sBegin = SName("begin")
val sVoid = SName("void")
val sIf = SName("if")
val sIfZero = SName("if-zero")
val sCond = SName("cond")
val sElse = SName("else")
val sRightArrow = SName("=>")
val sAnd = SName("and")
val sOr = SName("or")
val sValues = SName("values")
val sLetValues = SName("let-values")
val sVector = SName("vectorLiteral")


type exp
  SelfLit(lit: sexpr)
  QuoteLit(lit: sexpr)
  Ref(name: sexpr)
  App(f: exp, args: list<exp>)
  KLambda(formals: formals, body: body)
  ULambda(formals: formals, body: body)
  Lambda(formals: formals, body: body)
  IfE(test: exp, ifTrue: exp, ifFalse: exp)
  SetE(name: sexpr, value: exp)
  Values(vals: list<exp>)
  LetValues(bindings: list<binding>, body: body)
  Begin(body: body)
  And(exps: list<exp>)
  Or(exps: list<exp>)
  Cond(clauses: list<clause>)
  Undefined
  Void
  Let(bindings: list<binding>, body: body)
  LetStar(bindings: list<binding>, body: body)
  LetRec(bindings: list<binding>, body: body)

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

fun parseProgram(s: list<sexpr>): program
  Program(s.map(fn(e) e.parseDef))

fun parseDef(e: sexpr): def
  match e
    SList([SName("define"), SName(name), value]) ->
      VariableDef(SName(name), value.parseExp)
    SList(Cons(SName("define"), Cons(SList([SName(name), formals]), body))) ->
      FunctionDef(name, formals.parseFormals, body.parseBody)
    _ ->
      ImplicitDef(e.parseExp)

fun parseExpr(e: sexpr): exp
  return SelfLit(e)

fun show(p: program)
  p.defs.map(fn(d) d.show).join("\n")

fun show(d: def)
  match d
    ImplicitDef(value) ->
      value.show
    VariableDef(name, value) ->
      "(define " + name.show + " " + value.show + ")"
    FunctionDef(name, formals, body) ->
      "(define (" + name.show + " " + formals.show + ") " + body.show + ")"

fun show(e: exp)
  match e
    SelfLit(lit) ->
      lit.show
    QuoteLit(lit) ->
      "'" + lit.show
    Ref(name) ->
      name.show
    App(f, args) ->
      "(" + f.show + " " + args.map(fn(a) a.show).join(" ") + ")"
    KLambda(formals, body) ->
      "(lambda " + formals.show + " " + body.show + ")"
    ULambda(formals, body) ->
      "(λ " + formals.show + " " + body.show + ")"
    Lambda(formals, body) ->
      "(lambda " + formals.show + " " + body.show + ")"
    IfE(test, ifTrue, ifFalse) ->
      "(if " + test.show + " " + ifTrue.show + " " + ifFalse.show + ")"
    SetE(name, value) ->
      "(set! " + name.show + " " + value.show + ")"
    Values(vals) ->
      "(values " + vals.map(fn(v) v.show).join(" ") + ")"
    LetValues(bindings, body) ->
      "(let-values (" + bindings.map(fn(b) b.show).join(" ") + ") " + body.show + ")"
    Begin(body) ->
      "(begin " + body.show + ")"
    And(exps) ->
      "(and " + exps.map(fn(e) e.show).join(" ") + ")"
    Or(exps) ->
      "(or " + exps.map(fn(e) e.show).join(" ") + ")"
    Cond(clauses) ->
      "(cond " + clauses.map(fn(c) c.show).join(" ") + ")"
    Undefined ->
      "#<undefined>"
    Void ->
      "#<void>"
    Let(bindings, body) ->
      "(let (" + bindings.map(fn(b) b.show).join(" ") + ") " + body.show + ")"
    LetStar(bindings, body) ->
      "(let* (" + bindings.map(fn(b) b.show).join(" ") + ") " + body.show + ")"
    LetRec(bindings, body) ->
      "(letrec (" + bindings.map(fn(b) b.show).join(" ") + ") " + body.show + ")"

fun main()
  val s = parse.parseFile("test.scm")
  val p = parseProgram(s)
  println(p.show)
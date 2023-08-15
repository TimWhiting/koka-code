import analysis/p-analyzer/ir
import analysis/cps/sexpr
import newstd/data/linearmap

pub fun exception_context(c: string, f)
  with override final ctl throw-exn(exn)
    throw-exn(exn(message="\n\tWhile " ++ c  ++ ": " ++ exn.message))
  f()

pub type atom
  Id(s: symbol)
  Bool(b: bool)
  Number(n: int)
  Symbol(s: int)
  Lambda(args: list<symbol>, body: expr, is-bind-op: bool)

pub type expr
  Atom(a: atom)
  If(test: expr, consequent: expr, alternative: expr)
  Let(bindings: list<(symbol, expr)>, body: expr)
  Call(func: expr, arguments: list<expr>)
  Begin(expr: list<expr>)
  Set(name: symbol, value: expr)
  Struct(tag: int, field-values: list<expr>)
  Match(expr: expr, clauses: list<(int, list<symbol>, expr)>, default-clause: maybe<expr> = Nothing)
  SetField(struct-val: expr, field: int, new-value: expr)

value struct letForm
  bindings: list<(symbol, sexpr)>
  body: expr

pub type moduleItem
  TopLevel(e: expr)
  Define(name: symbol, value: expr)

effect scope
  fun scope-id(): int
  fun next-scope-id(): int

alias boundVars = linearMap<int, int>

fun int(x: sexpr): <exn> int
  match x
    SNumber(n) -> n.int
    _ -> throw("expected number")

fun tagged(x: sexpr): <exn> int
  match x
    SName(n) -> n.intern
    _ -> throw("expected symbol")

fun symbol(s: sexpr, bound-vars: boundVars): <exn> symbol
  match s
    SName(n) ->
      val i = n.intern
      val v = bound-vars.getDefault(i, 0)
      (i, v)
    _ ->
      throw("expected symbol")

fun split(expr: sexpr, message: string): <exn> (sexpr, sexpr)
  match expr
    SCons(e, rest) -> (e, rest)
    _ -> throw(message)

fun to-expr(a: atom): expr
  Atom(a)

fun parse(expr: sexpr): <div,exn> expr
  var scopeid := 0
  with handler
    fun scope-id() scopeid
    fun next-scope-id()
      scopeid := scopeid + 1
      scopeid
  parse_expr(expr, LinearMap([], fn(x: int, y: int) x == y))

fun parse_expr(expr: sexpr, bound-vars: boundVars): <div,exn,scope> expr
  match expr
    SCons(SName(s), rest) ->
      match s
        "λ" -> exception_context("parsing lambda", {parse_lambda(bound-vars, rest)})
        "lambda" -> exception_context("parsing lambda", {parse_lambda(bound-vars, rest)})
        "if" -> exception_context("parsing if", {parse_if(bound-vars, rest)})
        "set!" -> exception_context("parsing set!", {parse_set(bound-vars, rest)})
        "set-field!" -> exception_context("parsing set!", {parse_set_field(bound-vars, rest)})
        "begin" -> exception_context("parsing begin", {parse_begin(bound-vars, rest)})
        "let" -> exception_context("parsing let", {parse_let(bound-vars, rest)})
        "struct" -> exception_context("parsing struct", {parse_struct(bound-vars, rest)})
        "match" -> exception_context("parsing match", {parse_match(bound-vars, rest)})
        // Macros
        _ ->
          throw("not implemented lambda" ++ expr.show)
    SName(name) ->
      val s = name.intern
      Id((s, bound-vars.getDefault(s, 0))).to-expr
    SBool(b) -> Atom(Bool(b))
    SNumber(n) -> Atom(Number(n.int))
    SCons(f, rest) -> Call(f.parse_expr(bound-vars), rest.toList.map(fn(e) e.parse_expr(bound-vars)))
    _ ->
      throw("not implemented" ++ expr.show)
      // val rest = sexpr.cdr.as-cons()

fun parse_if(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (test, rest1) = rest.split("missing test expr")
  val (cons, rest2) = rest1.split("missing consequent expr")
  val (alt, rest3) = rest2.split("missing alternative expr")
  if !rest3.is-snil then
    throw("too many arguments")
  else
    If(test.parse_expr(bound-vars), cons.parse_expr(bound-vars), alt.parse_expr(bound-vars))

fun parse_set_field(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (s, rest1) = rest.split("missing struct")
  val (field-idx, rest2) = rest1.split("missing field")
  val (value, rest3) = rest2.split("missing value")
  if !rest3.is-snil then
    throw("too many arguments")
  else
    SetField(s.parse_expr(bound-vars), field-idx.int, value.parse_expr(bound-vars))

fun parse_struct(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (tag, rest1) = rest.split("missing struct tag")
  val exprs = rest1.toList.map(fn(e) e.parse_expr(bound-vars))
  Struct(tag.tagged, exprs)

fun parse_match(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  throw("unimplemented")

fun parse_let(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  throw("unimplemented")
  // val (bindings, rest1) = rest.split("let bindings")
  // val (body, rest2) = rest1.split("let body")
  // if !rest2.is-snil then
  //   throw("let has too many arguments")
  // else
    // Let(binds, body.parse_expr(bound-vars.addAll(binds.map(fn(s) s.fst))))

fun parse_set(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (name, rest1) = rest.split("missing name")
  val (value, rest2) = rest1.split("missing value")
  if !rest2.is-snil then
    throw("too many arguments")
  else
    Set(name.symbol(bound-vars), value.parse_expr(bound-vars))

fun parse_begin(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val exprs = rest.toList.map(fn(x) x.parse_expr(bound-vars))
  Begin(exprs)

fun parse_lambda(bound-vars, rest): <div,exn,scope> expr
  match rest
    SCons(args, SCons(bd, SNil)) ->
      val new-scope-id = next-scope-id()
      val argSyms = args.toList.map(fn(SName(s)) (s.intern, new-scope-id))
      val new-bound-vars = bound-vars.addAll(argSyms)
      with exception_context("parsing body")
      val body = bd.parse_expr(new-bound-vars)
      Atom(syntax/Lambda(argSyms, body, False))
    _ -> throw("missing args and body")

fun show(e: expr): <div> string
  match e
    Atom(a) -> show(a)
    syntax/If(test, consequent, alternative) ->
      "(if " ++ show(test) ++ " " ++ show(consequent) ++ " " ++ show(alternative) ++ ")"
    Let(bindings, body) ->
      "(let (" ++ bindings.map(fn((name, value)) name.to-sexp.show ++ " = " ++ show(value)).join(", ") ++ ") " ++ show(body) ++ ")"
    syntax/Call(func, arguments) ->
      "(" ++ show(func) ++ " " ++ arguments.map(show).join(" ") ++ ")"
    Begin(expr) ->
      "(begin " ++ expr.map(show).join(" ") ++ ")"
    syntax/Set(name, value) ->
      "(set! " ++ name.to-sexp.show ++ " " ++ show(value) ++ ")"
    Struct(tag, field-values) ->
      "(struct " ++ tag.show ++ " " ++ field-values.map(show).join(" ") ++ ")"
    syntax/Match(expr, clauses, default-clause) ->
      "(match " ++ show(expr) ++ " " ++ 
        clauses.map(fn((tag, vars, body)) "(" ++ tag.show ++ " " ++ vars.map(fn(v) v.to-sexp.show).join(" ") ++ body.show ++ ")").join("\n\t") ++
        default-clause.map(fn(v) -> "_ " ++ v.show).default("") ++ ")"
    syntax/SetField(s, field, value) ->
      "(set-field! " ++ s.show ++ " " ++ field.show ++ " " ++ value.show ++ ")"

fun show(a: atom): <div> string
  match a
    Id(s) -> s.to-sexp.show
    Bool(b) -> if b then "#t" else "#f"
    Number(n) -> n.show
    Symbol(s) -> s.unintern
    syntax/Lambda(args, body) ->
      "(lambda (" ++ args.map(fn(a1) a1.to-sexp.show).join(" ") ++ ") " ++ body.show ++ ")"

fun main()
  val expr = parse(parseProgramFromString("(lambda (x) (if #t #f))").head.default(SNil()))
  println(expr.show)
  println("done")
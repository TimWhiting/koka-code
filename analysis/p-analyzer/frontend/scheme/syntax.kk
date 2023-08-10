import analysis/p-analyzer/ir
import analysis/cps/sexpr
import newstd/data/linearmap

pub type atom
  Id(s: symbol)
  Bool(b: bool)
  Number(n: int)
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

struct letForm
  bindings: list<(symbol, sexpr)>
  new-bound-vars: list<(int, int)>
  body: expr

fun to-expr(a: atom): expr
  Atom(a)

effect scope
  fun scope-id(): int
  fun next-scope-id(): int

fun parse(expr: sexpr): <div,exn> expr
  var scopeid := 0
  with handler
    fun scope-id() scopeid
    fun next-scope-id()
      scopeid := scopeid + 1
      scopeid
  parse_expr(expr, LinearMap([], fn(x: int, y: int) x == y))

fun parse_expr(expr: sexpr, bound-vars: linearMap<int, int, <div,exn,scope>>): <div,exn,scope> expr
  match expr
    SName(name) ->
      val s = name.intern
      Id((s, bound-vars.getDefault(s, 0))).to-expr
    SBool(b) -> Atom(Bool(b))
    SNumber(n) -> Atom(Number(n.int))
    SCons(SName(s), rest) ->
      if (s == "λ" || s == "lambda") then
        parse_lambda(bound-vars, rest)
      else
        throw("not implemented lambda" ++ expr.show)
    _ ->
      throw("not implemented" ++ expr.show)
      // val rest = sexpr.cdr.as-cons()

fun parse_lambda(bound-vars, rest): <div,exn,scope> expr
  match rest
    SCons(args, SCons(bd, SNil)) ->
      val new-scope-id = next-scope-id()
      val argSyms = args.toList.map(fn(SName(s)) (s.intern, new-scope-id))
      val new-bound-vars = bound-vars.addAll(argSyms)
      trace(bd.show)
      val body = bd.parse_expr(new-bound-vars)
      Atom(syntax/Lambda(argSyms, body, False))
    _ -> throw("Expected lambda args and body")

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

fun show(a: atom): <div> string
  match a
    Id(s) -> s.to-sexp.show
    Bool(b) -> if b then "#t" else "#f"
    Number(n) -> n.show
    syntax/Lambda(args, body) ->
      "(lambda (" ++ args.map(fn(a1) a1.to-sexp.show).join(" ") ++ ") " ++ body.show ++ ")"

fun main()
  val expr = parse(parseProgramFromString("(lambda (x) x)").head.default(SNil()))
  println(expr.show)
  println("done")
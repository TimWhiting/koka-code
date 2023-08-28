import analysis/p-analyzer/ir
import analysis/cps/sexpr
import newstd/data/linearmap
import newstd/data/linearset
import macros

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
  String(s: string)
  If(test: expr, consequent: expr, alternative: expr)
  Let(bindings: list<(symbol, expr)>, body: expr)
  Call(func: expr, arguments: list<expr>)
  Begin(expr: list<expr>)
  Set(name: symbol, value: expr)
  Struct(tag: int, field-values: list<expr>)
  Match(expr: expr, clauses: list<(int, list<symbol>, expr)>, default-clause: maybe<expr> = Nothing)
  SetField(struct-val: expr, field: int, new-value: expr)

pub type moduleItem
  TopLevel(e: expr)
  Define(name: symbol, value: expr)

pub rec type parserExt
  ParserExt
    parse-id: (sexpr) -> <exn,scope> symbol = (fn (s) s.symbol(noBoundVars))
    custom-expr: (sexpr, boundVars) -> maybe<expr> = fn(s, bv) Nothing
    custom-module-item: (sexpr) -> maybe<moduleItem> = fn(s) Nothing
    preload-definitions: () -> list<moduleItem> = fn() []

effect scope
  fun scope-id(): int
  fun next-scope-id(): int
  val ext: parserExt
  fun next-macro-id(): int
  val macros: linearMap<string, syntaxRules>
  val reservedStrings: linearSet<string>
  final ctl unboundGlobal(s: string): a

alias boundVars = linearMap<int, int>
val noBoundVars = LinearMap([], fn(x: int, y: int) x == y)

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

fun new-symbol(s: sexpr): <exn,scope> symbol
  match s
    SName(n) ->
      (n.intern, scope-id())
    _ ->
      throw("expected symbol")

fun split(expr: sexpr, message: string): <exn> (sexpr, sexpr)
  match expr
    SCons(e, rest) -> (e, rest)
    _ -> throw(message)

fun splitEnd(expr: sexpr, message: string): <exn> (sexpr, sexpr)
  match expr
    SCons(e1, SCons(e2, SNil)) -> (e1, e2)
    _ -> throw(message)

fun to-expr(a: atom): expr
  Atom(a)

fun parse_lambda(bound-vars, rest): <div,exn,scope> expr
  val (args, bd) = rest.splitEnd("lambda expects args and body")
  val new-scope-id = next-scope-id()
  val argSyms = args.toList.map(fn(SName(s)) (s.intern, new-scope-id))
  val new-bound-vars = bound-vars.addAll(argSyms)
  with exception_context("parsing body")
  val body = bd.parse_expr(new-bound-vars)
  Atom(syntax/Lambda(argSyms, body, False))

fun parse_set(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (name, rest1) = rest.split("missing name")
  val (value, rest2) = rest1.split("missing value")
  if !rest2.is-snil then
    throw("too many arguments")
  else
    Set(name.symbol(bound-vars), value.parse_expr(bound-vars))

fun parse_set_field(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (s, rest1) = rest.split("missing struct")
  val (field-idx, rest2) = rest1.split("missing field")
  val (value, rest3) = rest2.split("missing value")
  if !rest3.is-snil then
    throw("too many arguments")
  else
    SetField(s.parse_expr(bound-vars), field-idx.int, value.parse_expr(bound-vars))

fun parse_begin(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val exprs = rest.toList.map(fn(x) x.parse_expr(bound-vars))
  Begin(exprs)

fun parse_struct(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (tag, rest1) = rest.split("missing struct tag")
  val exprs = rest1.toList.map(fn(e) e.parse_expr(bound-vars))
  Struct(tag.tagged, exprs)

fun parse_match(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (expr, clauses) = rest.split("missing match expr or clauses")
  parse_match_clauses(parse_expr(expr, bound-vars), bound-vars, clauses.toList())

fun parse_match_clauses(e: expr, b: boundVars, clauses: list<sexpr>): <div,exn,scope> expr
  var def := Nothing
  var cls := Nil
  clauses.foreach fn(c)
    val (pattern, rest) = c.split("Missing pattern or consequent expression")
    match pattern
      SCons(tag, bindings) ->
        match tag
          SName("_") ->
            def := Just(parse_expr(rest, b))
          _ ->
            val t = tag.tagged
            val id = next-scope-id()
            val binds = bindings.toList().map(fn(bind) (bind.tagged, id))
            val body = exception_context("expect body for match pattern")
              parse_expr(rest, b.addAll(binds))
            cls := Cons((t, binds, body), cls)
      _ -> throw("Expected pattern")
  Match(e, cls, def)

fun parse_if(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val (test, rest1) = rest.split("missing test expr")
  val (cons, rest2) = rest1.split("missing consequent expr")
  val (alt, rest3) = rest2.split("missing alternative expr")
  if !rest3.is-snil then
    throw("too many arguments")
  else
    If(test.parse_expr(bound-vars), cons.parse_expr(bound-vars), alt.parse_expr(bound-vars))

fun parse_let(bound-vars: boundVars, rest:sexpr): <div,exn,scope> expr
  val id = next-scope-id()
  val (bindings, body) = rest.splitEnd("expecting bindings and body in let form")
  val binds = bindings.toList.map fn(bind) 
    val (b, v) = bind.splitEnd("expecting binding name and value")
    (b.new-symbol(), v)
  val newBinds = bound-vars.addAll(binds.map(fn(s) s.fst))
  Let(binds.map(fn((bind, expr)) (bind, parse_expr(expr, newBinds))), body.parse_expr(newBinds))

fun make_quoted(v: sexpr): exn expr
  match v
    SNil -> Struct("empty".intern, [])
    SCons(car, cdr) -> Struct("cons".intern, [make_quoted(car), make_quoted(cdr)])
    SBool(b) -> Atom(Bool(b))
    SNumber(n) -> Atom(Number(n.int))
    SName(_) -> Atom(Id(v.symbol(noBoundVars)))
    SString(s) -> String(s)
    _ -> throw("not implemented")

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

fun parse(expr: sexpr): <div,exn> expr
  var scopeid := 0
  var macroid := 0
  with handler
    fun scope-id() scopeid
    fun next-scope-id()
      scopeid := scopeid + 1
      scopeid
    val ext = ParserExt()
    fun next-macro-id()
      macroid := macroid + 1
      macroid
    val macros = LinearMap([], fn(x: string, y: string) x == y)
    val reservedStrings = LinearSet(["define", "lambda", "if", "set!", "set-field!", "begin", "let", "struct", "match"], fn(s1, s2) s1 == s2)
    fun unboundGlobal(s)
      throw("unbound global " ++ s)
  parse_expr(expr, noBoundVars)

fun show(e: expr): <div> string
  match e
    Atom(a) -> show(a)
    String(s) -> s
    syntax/If(test, consequent, alternative) ->
      "(if " ++ show(test) ++ " " ++ show(consequent) ++ " " ++ show(alternative) ++ ")"
    Let(bindings, body) ->
      "(let (" ++ bindings.map(fn((name, value)) "(" ++ name.to-sexp.show ++ " " ++ show(value) ++ ")").join(", ") ++ ") " ++ show(body) ++ ")"
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
  val sexpr = parseProgramFromString("(let ((x 1)) (if x #t #f))").head.default(SNil())
  sexpr.show.println
  val expr = parse(sexpr)
  println(expr.show)
  println("done")
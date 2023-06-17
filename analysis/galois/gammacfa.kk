import list

type expr
  Lam(arg: list<string>, expr: expr)
  App(func: expr, arg: list<expr>)
  Var(name: string)

type cexpr
  CVar(name: string)
  CLam(args: list<string>, call: ccall)
  CEnd
  CErr(s: string)

type ccall
  CallC(func: cexpr, args: list<cexpr>)

effect fresh
  fun fresh(): string

effect val cont: cexpr

fun cpsl(vs': list<string>, es': list<expr>, kont: cexpr): <fresh,pure> ccall
  match (vs', es')
    (Nil,Nil) -> throw("cpsl: mismatched lists") 
    (Cons(v, Nil), Cons(e, Nil)) -> cps(e, CVar(v))
    (Cons(v, vs), Cons(e, es)) -> cps(e, CLam([v], cpsl(vs, es, kont)))
    (_, _) -> throw("cpsl: mismatched lists")
      

fun cps(expr: expr, kont: cexpr=CEnd): <fresh,pure> ccall
  val v = match expr
    Var(n) -> 
      CallC(kont, [CVar(n)])
    Lam(v, e) -> 
      val v' = fresh()
      // ("Tranferring lam for " ++ v.show).trace
      // CallC(kont, [CLam(v ++ [v'], cps(e, CVar(v')))]).show.trace
      CallC(kont, [CLam(v ++ [v'], cps(e, CVar(v')))])
    App(f, Cons(e, Nil)) ->
      val v' = fresh()
      val v = fresh()
      cps(f,CLam([v'], cps(e, CLam([v], CallC(CVar(v'), [CVar(v), kont])))))
    App(f, es)
      val v = fresh()
      val vs = es.map(fn(_) fresh())
      val r = cpsl(vs, es, kont)
      cps(f, CLam([v], CallC(CVar(v), vs.map(fn(v') CVar(v')))))
  v

fun handlefresh(f)
  var n := 0
  handle(f)
    fun fresh()
      n := n + 1
      "a" ++ n.show

type evalue
  EVal(e: cexpr, p: list<(string,evalue)>)

fun appprog(CallC(f, args), env: list<(string,evalue)> = []): div evalue
  val f' = eval(f, env)
  val args' = args.map(fn(a) eval(a, env))
  match f'
    EVal(CLam(a, b), p) -> 
      val env' = (a.zip(args')).foldl(p, fn(acc,(k,v)) acc.setVal(k,v,(==)))
      appprog(b, env')
    EVal(CEnd, _) -> args'.last.default(defErr("No result"))
    _ -> defErr("Not a function: " ++ f'.show)

fun defErr(s: string) 
  EVal(CErr(s), [])

fun eval(c: cexpr, env: list<(string,evalue)>): div evalue
  match c
    CVar(s) -> env.getKeyDefault(s, (==), defErr("Variable not found: " ++ s))
    CLam(a, b) -> EVal(CLam(a,b), env)
    CErr(s) -> EVal(CErr(s), [])
    CEnd -> EVal(CEnd, [])

fun fullEval(c: expr, showexpr: bool = False)
  if showexpr
    c.show.println
  val translation = cps(c)
  if showexpr
    translation.show.println
  translation.appprog.show.println

fun docps()
  with handlefresh
  cps(App(Var("x"), [Var("y"), Var("z")])).show.println
  // Var("x").fullEval(showexpr=True)
  // Lam(["x"], Var("x")).fullEval(showexpr = True)
  // App(Lam(["x"], Var("x")), [Lam(["y"], Var("y"))]).fullEval(showexpr = True)
  // App(Var("*"), [App(Var("+"), [Var("w"), Var("x")]), App(Var("-"), [Var("y"), Var("z")])]).fullEval(showexpr = True)

fun show(r: evalue): div string
  match r
    EVal(c, _) ->
      match c
        CLam([a,b], CallC(CVar(x), expr)) ->
          if b == x then
            if expr.length == 1 then
              "(\\" ++ a ++ ". " ++ show(expr.head.default(CErr("no lambda body?"))) ++ ")"
            else
              "(\\" ++ a ++ ". " ++ expr.map(show).join(" ") ++ ")"
          else 
            show(c)
        _ -> show(c)

fun show(c: cexpr): <div> string
  match c
    CVar(n) -> n
    CLam([a], call) -> "(\\" ++ a ++ ". " ++ show(call) ++ ")"
    CLam(args, call) -> "(\\" ++ args.join(".") ++ ". " ++ show(call) ++ ")"
    CEnd -> "end"
    CErr(s) -> "Error: " ++ s

fun show(call: ccall): <div> string
  match call
    CallC(func, args) -> "(" ++ show(func) ++ " " ++ args.map(show).join(" ") ++ ")"

fun show(expr: expr): div string
  match expr
    Var(n) -> n
    Lam([a], e) -> "(\\" ++ a ++ ". " ++ show(e) ++ ")"
    Lam(args, e) -> "(\\" ++ args.join(".") ++ ". " ++ show(e) ++ ")"
    App(f, args) -> "(" ++ show(f) ++ " " ++ args.map(show).join(" ") ++ ")"

fun main()
  docps()
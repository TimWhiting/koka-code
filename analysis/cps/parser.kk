import sexpr
import syntax
import std/data/linearset
import std/os/path
import std/os/file
import std/os/dir
import std/os/process

fun parseBindings(bds: sexpr): pure list<binding>
  // trace("Bindings " ++ bds.show)
  bds.toList.map(fn(b) b.parseBinding)

fun parseBinding(s: sexpr): pure binding
  match s
    SCons(name, SCons(exp, SNil())) -> (name, exp.parseExpr)
    _ -> throw("Binding with no expression " ++ s.show)


fun parseDef(e: sexpr): pure def
  // trace("Def " ++ e.show)
  match e
    SCons(SName("define"), SCons(SName(name), value)) ->
      DefVar(SName(name), value.parseExpr)
    SCons(SName("define"), SCons(SCons(SName(name), formals), body)) ->
      DefFun(SName(name), formals.parseFormals, body.toList.parseBody)
    _ ->
      DefImplicit(e.parseExpr)

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


fun parseQuasiquote(e: sexpr, depth:int=1): pure exp
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

// fun main()
//   val dir = run-system-read("pwd").maybe
//   val cwd = dir.map(fn(x) x.split(" ").last.default("").trim()).default("")
//   val searchDir = cwd.path / "higher-order-programs/scheme".path
//   println(searchDir.string)
//   try({
//     list-directory-recursive(searchDir).foreach fn(p)
//       if is-file(p) then // nbody
//         val fName = p.string
//         if fName.ends-with(".scm").is-just then
//           println(fName)
//           if fName.ends-with("nbody.scm").is-just || fName.ends-with("nucleic-2.scm").is-just then
//             ()
//           else // if p.string.ends-with("scheme-to-c.scm").is-just then
//             val s = parseFile(fName) // p.string)
//             val pr = parseProgram(s)
//             pr.free.foreach(fn(x) x.show.println)
//             pr.label.println
//             ()
//           // else
//           //   () // println(pr.show)
//     },fn(e) {println("Error " ++ e.show)})
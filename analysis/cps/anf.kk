import std/data/linearset
import std/os/path
import std/os/file
import std/os/dir
import std/os/process
import parsers/regex/sexpr
import syntax
import parser

alias ekont = exp -> pure exp

fun toLetRec(b: body): pure exp
  LetRec(b.defs.map(fn(x) (x.name, x.value)), Body([], b.exps))

fun normalize(b: body): pure body
  b.toLetRec.body

fun normalizeBody(b: body, k: ekont): pure body
  val d = b.defs.map(normalize)
  match b.exps.reverse
    [x] -> Body(d, [x.normalizeExp(k)])
    Cons(last, front) -> Body(d, front.map(normalize).reverse ++ [last.normalizeExp(k)])
    [] -> throw("empty body")

fun def/normalize(d: def): pure def
  match d
    DefImplicit(value) -> DefImplicit(value.normalize)
    DefVar(name, value) -> DefVar(name, value.normalize)
    DefFun(name, formals, body) -> DefFun(name, formals, body.normalize)

fun let(e: exp, k: ekont): pure exp
  match e
    SelfLit() -> k(e)
    QuoteLit() -> k(e)
    Ref() -> k(e)
    Void() -> k(e)
    Undefined() -> k(e)
    _ ->
      val tmp = genName("$tmp")
      Let([(tmp, e)], Body([], [k(Ref(tmp))]))

fun exp/normalize(e: exp): pure exp
  e.normalizeExp(fn(x) x)

fun normalizeName(e: exp, k: ekont): pure exp
  e.normalizeExp(fn(x) if x.isAtomic && x.isDuplicable then k(x) else x.let(k))

fun normalizeExp(e: exp, k: ekont): pure exp
  match e
    Ref() -> k(e)
    SelfLit() -> k(e)
    QuoteLit() -> k(e)
    Undefined() -> k(e)
    Void() -> k(e)
    Lambda(formals, body) -> k(Lambda(formals, body.normalize))
    IfE(condition, ifTrue, ifFalse) -> condition.normalizeName(fn(cond) IfE(cond, ifTrue.normalize, ifFalse.map(normalize)))
    Cond() -> e.toIf.normalizeExp(k)
    Or() -> e.toIf.normalizeExp(k)
    And() -> e.toIf.normalizeExp(k)
    Let([], body) -> Begin(body.normalizeBody(k))
    _ -> throw("Normalize " ++ e.show ++ " not implemented!")

fun exp/toIf(e: exp): pure exp
  match e
    IfE() -> e
    Cond(clauses) -> clauses.toIf
    _ -> e

fun clause/toIf(l: list<clause>): pure exp
  match l
    Cons(SelfClause(test), tail) -> test.let(fn(v) IfE(v, v, Just(tail.toIf)))
    Cons(ElseClause(exps)) -> Begin(Body([], exps))
    Cons(TestClause(test, exps), tail) -> IfE(test, Begin(Body([], exps)), Just(tail.toIf))
    [] -> Void()

fun main()
  val dir = run-system-read("pwd").maybe
  val cwd = dir.map(fn(x) x.split(" ").last.default("").trim()).default("")
  val searchDir = cwd.path / "higher-order-programs/scheme".path
  println(searchDir.string)
  try({
    list-directory-recursive(searchDir).foreach fn(p)
      if is-file(p) then // nbody
        val fName = p.string
        if fName.ends-with(".scm").bool then
          println(fName)
          if ["nbody", "nucleic-2"].any(fn(f) fName.ends-with(f ++ ".scm").bool) then
            ()
          else // if p.string.ends-with("scheme-to-c.scm").is-just then
            val s = parseFile(fName) // p.string)
            val pr = parseProgram(s)
            pr.toExp.normalize
            ()
          // else
          //   () // println(pr.show)
    },fn(e) {println("Error " ++ e.show)})
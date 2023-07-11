import parser
import sexpr
import syntax
import std/os/path
import std/os/file
import std/os/dir
import std/os/process

alias ekont = exp -> pure exp
fun toLetRec(b: body): pure exp
  LetRec(b.defs.map(fn(x) (x.name, x.value)), b.exps)

fun normalize(b: body): pure body
  b.toLetRec.body

fun normalizeBody(b: body, k: ekont): pure body
  val d = b.defs.map(normalize)
  match b.exps.reverse
    [x] -> Body(d, [x.normalizeExp(k)])
    Cons(last, front) -> Body(d, front.map(normalize).reversed ++ [last.normalizeExp(k)])
    [] -> throw("empty body")

fun normalize(d: def): pure def
  match d
    DefImplicit(value) -> DefImplicit(value.normalize)
    DefVar(name, value) -> DefVar(name, value.normalize)
    DefFun(name, formals, body) -> DefFun(name, formals, body.normalize)

fun let(e: exp, k: ekont): pure exp
  match e
    ILit() -> k(e)
    Ref() -> k(e)
    Void() -> k(e)
    Undefined() -> k(e)
    _ ->
      val tmp = genName("$tmp")
      Let([(tmp, e)], Body([], [k(Ref(tmp))]))

fun normalize(e: exp): pure exp
  e.normalizeExp(fn(x) x)

fun normalizeName(e: exp, k: ekont): pure exp
  e.normalizeExp(fn(x) if x.isAtomic && x.isDuplicable then k(x) else x.let(k))

fun normalizeExp(e: exp, k: ekont): pure exp
  match e
    Ref() -> k(e)
    ILit() -> k(e)
    Undefined() -> k(e)
    Void() -> k(e)
    Lambda(formals, body) -> k(Lambda(formals, body.normalize))
    IfExp(condiiton, ifTrue, ifFalse) -> condition.normalizeName(fn(cond) k(IfExp(cond, ifTrue.normalize, ifFalse.map(normalize))))
    Cond() -> e.toIf.normalizeExp(k)
    Or() -> e.toIf.normalizeExp(k)
    And() -> e.toIf.normalizeExp(k)
    _ -> throw("Unimplemented")

fun main()
  val dir = run-system-read("pwd").maybe
  val cwd = dir.map(fn(x) x.split(" ").last.default("").trim()).default("")
  val searchDir = cwd.path / "higher-order-programs/scheme".path
  println(searchDir.string)
  try({
    list-directory-recursive(searchDir).foreach fn(p)
      if is-file(p) then // nbody
        val fName = p.string
        if fName.ends-with(".scm").is-just then
          println(fName)
          if fName.ends-with("nbody.scm").is-just || fName.ends-with("nucleic-2.scm").is-just then
            ()
          else // if p.string.ends-with("scheme-to-c.scm").is-just then
            val s = parseFile(fName) // p.string)
            val pr = parseProgram(s)
            pr.toExp.normalize
            ()
          // else
          //   () // println(pr.show)
    },fn(e) {println("Error " ++ e.show)})
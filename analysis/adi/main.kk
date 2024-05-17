import ev
import abev
import expr
import utils
import cache
import std/data/linearmap
import std/data/linearset

fun test-abstract-normal(e)
  test-abstract(evnormalabs, e).show(show).trace

fun handleTellAbs(f)
  with handler
    fun tell(x, depth)
      val (a:expr, b:env<int>, c:linearMap<int,abvalue<int>>) = x
      val indent = " ".repeat(depth)
      val indent2 = " ".repeat(depth+1)
      (indent ++ "Config: \n" ++ indent2 ++ "expr:" ++ a.show ++ "\n" ++ indent2 ++ "env:" ++ b.show(show) ++ "\n" ++ indent2 ++ "store:" ++ c.list.show(show)).trace
    fun tellResult(s:abvalue<int>, depth)
      (" ".repeat(depth) ++ "Result: " ++ s.show(showA)).trace
      s
    val expressionDepth = 0
  f()

fun test-cache-abs(e: expr)
  fixcache(docacheev, e)

fun test-cachetell-abs(e: expr)
  with handleTellAbs
  fixcache(docachetell, e)

fun test-evtell-abs(e)
  with handleTellAbs
  test-abstract(doevtellabs, e)

fun test-abs(e)
  test-abstract(evnormalabs, e)

fun test-evtell(e)
  with handler
    fun tell(x, depth)
      val (a:expr, b:env<int>, c:linearMap<int,evalue<int>>) = x
      (" ".repeat(depth) ++ a.show ++ "," ++ b.show(show) ++ "," ++ c.list.show(show)).trace
    fun tellResult(s:evalue<int>, depth)
      (" ".repeat(depth) ++ "Result: " ++ s.show).trace
      s
    val expressionDepth = 0
  test-concrete(doevtell, e)

fun test-evdead(e)
  var dead := linearSet(e.subexprs, fn(a: expr, b: expr) a == b, fn(a: expr) a.show)
  with handler
    fun get-dead()
      dead
    fun mark-alive(e1)
      dead := dead - e1
  val r = test-concrete(doevdead, e)
  trace("The following are dead expressions")
  dead.list.show-list(show).trace
  trace("Result of the program " ++ r.show)

fun test-concrete-variations()
  test-concrete(doevnormal, App(Rec("fact", Lam("n", If0(Id("n"), Num(1), Op2("*", Id("n"), App(Id("fact"), Op2("-", Id("n"), Num(1))))))), Num(10))).show.trace
  test-evtell(Op2("*", Op2("+", Num(3), Num(4)), Num(9))).show.trace
  // (if0 0 1 2)
  test-evdead(If0(Num(0), Num(1), Num(2)))
  // (lambda (x) x)
  test-evdead(Lam("x", Id("x")))
  // (if0 (/ 1 0) 2 3)
  test-evdead(If0(Op2("/", Num(1), Num(0)), Num(2), Num(3)))

fun main()
  test-concrete-variations()
  // (let ((f (lambda (x) x))) (f 1) (f 2))
  test-evtell-abs(Let("f", Lam("x", Id("x")), [App(Id("f"), Num(1) ), App(Id("f"), Num(2))])).show(show).trace
  // ((rec f (λ (x) (f x))) 0)
  // "Should be empty, due to infinite recursion".println
  test-cache-abs(App(Rec("f", Lam("x", App(Id("f"), Id("x")))), Num(0))).show(show).trace
  // ((rec f (λ (n) (if0 n 1 (* n (f (- n 1)))))) 5)
  test-cache-abs(doNormalize(App(Rec("f", Lam("n", If0(Id("n"), Num(1), Op2("*", Id("n"), App(Id("f"), Op2("-", Id("n"), Num(1))))))), Num(5)))).show(show).trace
  // Should be 'N
  // ((rec f (λ (x) (if0 x 0 (if0 (f (- x 1)) 2 3)))) (+ 1 0))
  test-cache-abs(doNormalize(App(Rec("f", Lam("x", If0(Id("x"), Num(0), If0(App(Id("f"), Op2("-", Id("x"), Num(1))), Num(2), Num(3)) ))), Op2("+", Num(1), Num(0))))).show(show).trace
  // Should be {2, 0, 3} // Depending on how the abstract numbers and nondeterminism are implemented -- should actually be 'N
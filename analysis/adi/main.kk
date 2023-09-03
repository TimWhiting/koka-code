import ev
import abev
import expr
import utils
import cache
import newstd/data/linearmap
import newstd/data/linearset

fun test-abstract-normal(e)
  test-abstract(evnormalabs, e).show(show).println

fun handleTellAbs(f)
  with handler
    fun tell(x)
      val (a:expr, b:env<int>, c:linearMap<int,abvalue<int>>) = x
      ("Config: \n\texpr:" ++ a.show ++ "\n\tenv:" ++ b.show(show) ++ "\n\tstore:" ++ c.list.show(show) ++ "\n").trace
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
    fun tell(x)
      val (a:expr, b:env<int>, c:linearMap<int,evalue<int>>) = x
      (a.show ++ "," ++ b.show(show) ++ "," ++ c.list.show(show)).println
  test-concrete(doevtell, e)

fun test-evdead(e)
  var dead := linearSet(e.subexprs, fn(a: expr, b: expr) a == b, fn(a: expr) a.show)
  with handler
    fun get-dead()
      dead
    fun mark-alive(e1)
      dead := dead - e1
  val r = test-concrete(doevdead, e)
  println("The following are dead expressions")
  dead.list.show-list(show).println
  println("Result of the program " ++ r.show)

fun test-concrete-variations()
  test-concrete(doevnormal, App(Rec("fact", Lam("n", If0(Id("n"), Num(1), Op2("*", Id("n"), App(Id("fact"), Op2("-", Id("n"), Num(1))))))), Num(10))).show.println
  test-evtell(Op2("*", Op2("+", Num(3), Num(4)), Num(9))).show.println
  // (if0 0 1 2)
  test-evdead(If0(Num(0), Num(1), Num(2)))
  // (lambda (x) x)
  test-evdead(Lam("x", Id("x")))
  // (if0 (/ 1 0) 2 3)
  test-evdead(If0(Op2("/", Num(1), Num(0)), Num(2), Num(3)))

fun main()
  test-concrete-variations()
  // (let ((f (lambda (x) x))) (f 1) (f 2))
  test-evtell-abs(Let("f", Lam("x", Id("x")), [App(Id("f"), Num(1) ), App(Id("f"), Num(2))])).show(show).println
  // ((rec f (λ (x) (f x))) 0)
  // "Should be empty, due to infinite recursion".println
  test-cache-abs(App(Rec("f", Lam("x", App(Id("f"), Id("x")))), Num(0))).show(show).println
  // ((rec f (λ (n) (if0 n 1 (* n (f (- n 1)))))) 5)
  test-cache-abs(doNormalize(App(Rec("f", Lam("n", If0(Id("n"), Num(1), Op2("*", Id("n"), App(Id("f"), Op2("-", Id("n"), Num(1))))))), Num(5)))).show(show).println
  // Should be 'N
  // ((rec f (λ (x) (if0 x 0 (if0 (f (- x 1)) 2 3)))) (+ 1 0))
  test-cache-abs(doNormalize(App(Rec("f", Lam("x", If0(Id("x"), Num(0), If0(App(Id("f"), Op2("-", Id("x"), Num(1))), Num(2), Num(3)) ))), Op2("+", Num(1), Num(0))))).show(show).println
  // Should be {2, 0, 3} // Depending on how the abstract numbers and nondeterminism are implemented -- should actually be 'N
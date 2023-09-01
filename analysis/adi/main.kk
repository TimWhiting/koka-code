import ev
import abev
import expr
import utils
import newstd/data/linearmap
import newstd/data/linearset

fun test-evtell-abs(e)
  with handler
    fun tell(x)
      val (a:expr, b:env<int>, c:linearMap<int,abvalue<int>>) = x
      (a.show ++ "," ++ b.show(show) ++ "," ++ c.list.show(show)).println
  test-abstract(doevtell, e)

fun test-evtell(e)
  with handler
    fun tell(x)
      val (a:expr, b:env<int>, c:linearMap<int,evalue<int>>) = x
      (a.show ++ "," ++ b.show(show) ++ "," ++ c.list.show(show)).println
  test-concrete(doevtell, e)

fun test-evdead(e)
  var dead := linearSet(e.subexprs, fn(a: expr, b: expr) a == b)
  with handler
    fun get-dead()
      dead
    fun mark-alive(e1)
      dead := dead - e1
  val r = test-concrete(doevdead, e)
  println("The following are dead expressions")
  dead.list.show-list(show).println
  println("Result of the program " ++ r.show)

fun test-abstract-normal(e)
  test-abstract(doevtell, e).show(show).println

fun test-concrete-variations()
  test-concrete(evnormal, App(Rec("fact", Lam("n", If0(Id("n"), Num(1), Op2("*", Id("n"), App(Id("fact"), Op2("-", Id("n"), Num(1))))))), Num(10))).show.println
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
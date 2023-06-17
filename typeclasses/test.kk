import datastructure
import utils
import interp
import primitives
import infer

val eqI = Ident("eq")
val eqE = EVar(eqI, Just(createEqType(tAlpha).scheme))

val pE = eVar("p")
val qE = eVar("q")

val eqIntT = createEqType(tInt).scheme
val eqCharT = createEqType(tChar).scheme
val forAllEq = createEqType(tAlpha).scheme([alphaT])
val tupleEqT = 
  ForAll([alphaT, betaT],
    TPred(
      [(eqI, createEqType(tAlpha).classT), (eqI, createEqType(tBeta))],
      createEqType(TApp(tcTuple, [tAlpha, tBeta]))
    )
  )

fun inferEval(e: expr, evaluate: bool = False, out: bool = True)
  val res = doInfer(e, [], [])
  if out then res.show(show, show).println else ()
  if evaluate then res.fst.eval.show.println else ()
  res.fst

fun createEqFun(e: expr): expr
  Over(eqI, forAllEq, 
      Inst(eqI, eqIntT, eEqInt,
        Inst(eqI, eqCharT, eEqChar, e)))

fun assume(evaluate:bool = False)
  val eqE = EVar(eqI, Nothing)

  val assums = [
    Overloaded(eqI, forAllEq),
    Instance(eqI, eqIntT, eqI(signature = Just(eqIntT))),
    Instance(eqI, eqCharT, eqI(signature = Just(eqCharT))),
    Instance(eqI, tupleEqT, eqI(signature = Just(tupleEqT))),
    Variable(eqI, createEqType(tAlpha).scheme, eqI(signature = Just(createEqType(tAlpha).scheme))),
    Variable(eqI, createEqType(tBeta).scheme, eqI(signature = Just(createEqType(tBeta).scheme))),
  ]

  ForAll([alphaT], TPred([(eqI, createEqType(tAlpha))], TFun(tAlpha, tBool))).greater(TFun(tInt, tBool).scheme, assums).show.println()
  "\n\n\n".println
  ForAll([alphaT], TPred([(eqI, createEqType(tAlpha))], TFun(tAlpha, tBool))).greater(TFun(tFloat, tBool).scheme, assums).show.println()

  createEqFun(App(eqE, ETup([eInt(1), eInt(1)]))).inferEval(evaluate)
  createEqFun(App(eqE, ETup([eChar('a'), eChar('a')]))).inferEval(evaluate)


fun eqExample()
  val eqE = EVar(eqI, Nothing)
  val x = 
    Over(eqI, forAllEq, 
      Inst(eqI, eqIntT, eEqInt,
        Inst(eqI, eqCharT, eEqChar, 
          Inst(eqI, tupleEqT, 
            Lam(Ident("a"),
              Let(Ident("p"), App(eFst, eVar("a")),
                Let(Ident("q"), App(eSnd, eVar("a")),
                  App(eAnd,
                    ETup([
                      App(eqE, ETup([App(eFst, eVar("p")), App(eFst, eVar("q"))])),
                      App(eqE, ETup([App(eSnd, eVar("p")), App(eSnd, eVar("q"))])),
                    ])
                  )
                )
              )
            ),
            App(eqE, 
              ETup([
                ETup([eInt(1), eChar('a')]), 
                ETup([eInt(2), eChar('b')]),
              ])
            )
          )
        )
      )
    )
  // x.infer.show(show,show).println
  x.doInfer.fst.show.println
  // x.eval()

fun primitiveTests()
  App(eEqChar, ETup([eChar('b'), eChar('b')])).eval.show.println()
  App(eEqChar, ETup([eChar('b'), eChar('c')])).eval.show.println()
  App(eEqInt, ETup([eInt(1), eInt(1)])).eval.show.println()
  App(eEqInt, ETup([eInt(1), eInt(2)])).eval.show.println()
  App(eAddInt, ETup([eInt(1), eInt(2)])).eval.show.println()
  App(eMultInt, ETup([eInt(1), eInt(2)])).eval.show.println()
  App(eNegInt, eInt(1)).eval.show.println()
  App(eAddFloat, ETup([eFloat(1.5), eFloat(2.5)])).eval.show.println()
  App(eMultFloat, ETup([eFloat(1.5), eFloat(2.5)])).eval.show.println()
  App(eNegFloat, eFloat(1.0)).eval.show.println()

  val a = Ident("a")
  val eA = EVar(a)
  App(Lam(a, App(eA, ETup([eChar('b'), eChar('b')]))), eEqChar).eval.show.println()

fun inferTests()
  doInfer(ETup([eInt(1), eChar('a')])).show(show, show).println()
  doInfer(App(eEqChar, ETup([eChar('b'), eChar('b')]))).show(show, show).println()
  // doInfer(
  //   Let(Ident("test"), 
  //     Lam(Ident("x"), Lam(Ident("y"), 
  //       App(eAddInt, ETup([App(eMultInt, ETup([eVar("x"), eVar("x")])), App(eMultInt, ETup([eVar("y"), eVar("y")]))])))),
  //   App(App(eVar("test"), eInt(2)), eInt(3)))).fst.show.println()
  eqExample()

fun main()
  // notrace()
  // primitiveTests()
  // inferTests()
  assume(True)
  ()
  // eqExample()


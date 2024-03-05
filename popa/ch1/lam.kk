import common
import std/core/unsafe

type expr
  Var(x: variable, label:label=unsafe-total(unique))
  Num(n: int, label:label=unsafe-total(unique))
  Fn(x: variable, body: expr, label:label=unsafe-total(unique))
  App(e1: expr, e2: expr, label:label=unsafe-total(unique))
  PrimApp(x: variable, es: list<expr>, label:label=unsafe-total(unique))
  Let(x: list<(variable,expr)>, body: expr, label:label=unsafe-total(unique))

fun show(e: expr): div string
  match e
    Var(x, l) -> "[" ++ x.show ++ "]@" ++ l.show
    Num(n, l) -> n.show ++ "@" ++ l.show
    Fn(x, body, l) -> "[fn " ++ x.show ++ " => " ++ body.show ++ "]@" ++ l.show
    App(e1, e2, l) -> "[" ++ e1.show ++ " " ++ e2.show ++ "]@" ++ l.show
    PrimApp(x, es, l) -> "[" ++ x.show ++ " " ++ es.show ++ "]@" ++ l.show
    Let(x, body, l) -> "[let " ++ x.show ++ " in " ++ body.show ++ "]@" ++ l.show

// val ex0 = Let(
//   [
//     ("f", Fn("x", App(Var("x"), Num(1)))),
//     ("g", Fn("y", PrimApp("+", [Var("y"), Num(2)]))),
//     ("h", Fn("z", PrimApp("+", [Var("z"), Num(3)])))
//   ], 
//   PrimApp("+", [App(Var("f"), Var("g")), App(Var("f"), Var("h"))])
//   )

val ex1_2 = App(Fn("x", Var("x")), Fn("y", Var("y")))

fun example-show1_2()
  ex1_2.show.println 
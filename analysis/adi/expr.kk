import utils
import std/core-extras

type expr
  Num(i: int)
  If0(e0: expr, e1: expr, e2: expr)
  Op2(op: string, e0: expr, e1: expr)
  Id(x: string)
  Rec(x: string, e: expr)
  Lam(v: string, e: expr)
  App(e0: expr, e1: expr)
  Let(v: string, e0: expr, e1s: list<expr>)

fun show(e: expr): div string
  match e
    Num(n) -> n.show
    If0(e0, e1, e2) -> "if0 " ++ show(e0) ++ " then " ++ show(e1) ++ " else " ++ show(e2)
    Op2(op, e0, e1) -> "(" ++ show(e0) ++ " " ++ op ++ " " ++ show(e1) ++ ")"
    Id(x) -> x
    Rec(fname, e0) -> "rec " ++ fname ++ " = " ++ show(e0)
    Lam(v, e0) -> "fun " ++ v ++ " -> " ++ show(e0)
    App(e0, e1) -> "(" ++ show(e0) ++ " " ++ show(e1) ++ ")"  
    Let(v, e0, e1) -> "let " ++ v ++ " = " ++ show(e0) ++ " in " ++ show-list(e1, show)

fun (==)(e1: expr, e2: expr): div bool
  with traceEq(e1, e2) 
  match (e1, e2)
    (Num(i1), Num(i2)) -> i1 == i2
    (If0(e1, e2, e3), If0(e4, e5, e6)) -> e1 == e4 && e2 == e5 && e3 == e6
    (Op2(op1, e1, e2), Op2(op2, e3, e4)) -> op1 == op2 && e1 == e3 && e2 == e4
    (Id(x1), Id(x2)) -> x1 == x2
    (Rec(x1, e1), Rec(x2, e2)) -> x1 == x2 && e1 == e2
    (Lam(x1, e1), Lam(x2, e2)) -> x1 == x2 && e1 == e2
    (App(e1, e2), App(e3, e4)) -> e1 == e3 && e2 == e4
    (Let(x1, e1, e2), Let(x2, e3, e4)) -> x1 == x2 && e1 == e3 && eql/(==)(e2, e4)
    _ -> False

fun subexprs(e: expr): div list<expr>
  match e
    Num(_) -> [e]
    If0(e0, e1, e2) -> Cons(e, e0.subexprs ++ e1.subexprs ++ e2.subexprs)
    Op2(_, e0, e1) -> Cons(e, e0.subexprs ++ e1.subexprs)
    Id(_) -> [e]
    Rec(_, e0) -> Cons(e, e0.subexprs)
    Lam(_, e0) -> Cons(e, e0.subexprs)
    App(e0, e1) -> Cons(e, e0.subexprs ++ e1.subexprs)
    Let(_, e0, e1) -> Cons(e, e0.subexprs ++ e1.map(subexprs).concat)

effect unique
  fun uniq(): string

fun handleUnique(f)
  var u := 0
  with handler
    fun uniq()
      val n = "_" ++ u.show
      u := u + 1
      n
  f()

fun doNormalize(e: expr): div expr
  with handleUnique
  normalize(e)
      
fun normalize(e: expr): <unique,div> expr
  match e
    Num -> e
    If0(e0, e1, e2) -> If0(normalize(e0), normalize(e1), normalize(e2))
    Op2(op, Id(u1), Id(u2)) -> 
      Op2(op, Id(u1), Id(u2))
    Op2(op, Id(u1), e1) -> 
      val u2 = uniq()
      Let(u2, normalize(e1), [Op2(op, Id(u1), Id(u2))])
    Op2(op, e0, Id(u2)) -> 
      val u1 = uniq()
      Let(u1, normalize(e0), [Op2(op, Id(u1), Id(u2))])
    Op2(op, e0, e1) -> 
      val u1 = uniq()
      val u2 = uniq()
      Let(u1, normalize(e0), [Let(u2, normalize(e1), [Op2(op, Id(u1), Id(u2))])])
    Id -> e
    Rec(fname, e0) -> Rec(fname, normalize(e0))
    Lam(v, e0) -> Lam(v, normalize(e0))
    App(e0, e1) -> App(normalize(e0), normalize(e1))
    Let(v, e0, e1) -> Let(v, normalize(e0), e1.map(normalize))

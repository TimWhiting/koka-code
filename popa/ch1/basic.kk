import std/core/unsafe
import common

type opa
  OpAdd
  OpSub
  OpMult

fun opa/show(op: opa): string
  match op
    OpAdd -> "+"
    OpSub -> "-"
    OpMult -> "*"

type aexp
  Var(v: variable)
  Num(i: int)
  AExp(a1: aexp, op: opa, a2: aexp)

fun aexp/show(a: aexp): string
  match a
    Var(v) -> v
    Num(i) -> i.show
    AExp(a1, op, a2) -> a1.show ++ op.show ++ a2.show

type opb
  OpAnd
  OpOr

fun opb/show(op: opb): string
  match op
    OpAnd -> "&&"
    OpOr -> "||"

type opr
  OpEq
  OpLt
  OpGt

fun opr/show(op: opr): string
  match op
    OpEq -> "=="
    OpLt -> "<"
    OpGt -> ">"

type bexp
  BoolF
  BoolT
  Not(b: bexp)
  BExpr(b1: bexp, op: opb, b2: bexp)
  RExpr(a1: aexp, op: opr, a2: aexp)

fun bexp/show(e: bexp): string
  match e
    BoolF -> "false"
    BoolT -> "true"
    Not(b) -> "not " ++ b.show
    BExpr(b1, op, b2) -> b1.show ++ op.show ++ b2.show
    RExpr(a1, op, a2) -> a1.show ++ op.show ++ a2.show

type statement
  Sequence(fst: statement, snd: statement)
  If(cond: basicBlock, thenSt: statement, elseSt: statement)
  While(cond: basicBlock, doSt: statement)
  Basic(b: basicBlock)

fun statement/show(s: statement): div string
  match s
    Sequence(fst, snd) -> "(" ++ [fst, snd].map(show).join(";") ++ ")"
    If(cond, thenSt, elseSt) -> "if " ++ cond.show ++ " then " ++ thenSt.show ++ " else " ++ elseSt.show
    While(cond, doSt) -> "while " ++ cond.show ++ " do " ++ doSt.show
    Basic(b) -> b.show

type basicBlock
  Assign(v: variable, a: aexp, label: label = unsafe-total(unique))
  BBlock(b: bexp, label: label = unsafe-total(unique))
  Skip(label: label = unsafe-total(unique))  

fun basicBlock/show(b: basicBlock): string
  match b
    Assign(v, a, l) -> "[" ++ v ++ ":=" ++ a.show ++ "]@" ++ l.show
    BBlock(b, l) -> "[" ++ b.show ++ "]@" ++ l.show
    Skip(l) -> "skip@" ++ l.show

fun sequence(l: list<statement>): statement
  match l
    [] -> Skip().Basic
    Cons(x,Nil) -> x
    Cons(x, xs) -> Sequence(x, sequence(xs))

val example1_1 = [
  Assign("y", Var("x")).Basic,
  Assign("z", Num(1)).Basic,
  While(
    RExpr(Var("y"), OpGt, Num(1)).BBlock,
    Sequence(
      Assign("z", AExp(Var("z"), OpMult, Var("y"))).Basic,
      Assign("y", AExp(Var("y"), OpSub, Num(1))).Basic
    )
  ),
  Assign("y", Num(0)).Basic
].sequence

fun example-show()
  example1_1.show.println
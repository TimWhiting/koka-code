import ch1/basic
import ch1/common

fun init(s: statement): basicBlock
  match s
    Sequence(a) -> a.init
    While(c) -> c
    If(c) -> c
    Basic(b) -> b

fun finals(s: statement): div list<basicBlock>
  match s
    Basic(b) -> [b]
    Sequence(_,b) -> b.finals
    If(_,s1,s2) -> finals(s1) ++ finals(s2)
    While(c) -> [c]

fun blocks(s: statement): div list<basicBlock>
  match s
    Basic(b) -> [b]
    Sequence(a,b) -> a.blocks ++ b.blocks
    If(c, s1, s2) -> Cons(c, s1.blocks ++ s2.blocks)
    While(c, s) -> Cons(c, s.blocks)

fun labels(s: statement): div list<label>
  s.blocks.map(label)

fun flow(s: statement): div list<(label, label)>
  match s
    Basic -> []
    Sequence(hd,nxt) -> 
      hd.flow ++ nxt.flow ++ 
      hd.finals.map(fn(l) (l.label, nxt.init.label))
    If(c,s1,s2) -> 
      Cons((c.label, s2.init.label), 
        Cons((c.label, s1.init.label), 
          s1.flow ++ s2.flow))
    While(c,s) -> 
      Cons((c.label, s.init.label), 
        s.flow ++ s.finals.map(fn(l) (l.label, c.label)))

fun flowr(s: statement): div list<(label, label)>
  s.flow.map(fn((x, y)) (y, x))

val power = [
  Assign("z", Num(1), 1).Basic,
  While(
    RExpr(Var("x"), OpGt, Num(0)).BBlock(2),
    Sequence(
      Assign("z", AExp(Var("z"), OpMult, Var("y")), 3).Basic,
      Assign("x", AExp(Var("x"), OpSub, Num(1)), 4).Basic
    )
  )
].sequence
  
fun test-power()
  power.show.println
  power.init.println
  power.finals.println
  power.labels.println
  power.flow.println
  power.flowr.println

val example_2_4 = [
  Assign("x", AExp(Var("a"), OpAdd, Var("b")), 1).Basic,
  Assign("y", AExp(Var("a"), OpMult, Var("b")), 2).Basic,
  While(
    RExpr(Var("y"), OpGt, AExp(Var("a"), OpAdd, Var("b"))).BBlock(3),
    Sequence(
      Assign("a", AExp(Var("a"), OpAdd, Num(1)), 4).Basic,
      Assign("x", AExp(Var("a"), OpAdd, Var("b")), 5).Basic
    )
  )
].sequence


fun bb/vars(b: basicBlock): set<variable>
  match b
    Assign(v, e, _) -> e.vars.add(v)
    BBlock(e) -> e.vars
    Skip -> [].Set

fun aexp/vars(a: aexp): set<variable>
  match a
    Var(v) -> [v].Set
    AExp(a1, _, a2) -> a1.vars ++ a2.vars
    _ -> [].Set

fun bexp/vars(b: bexp): set<variable>
  match b
    RExpr(a1, _, a2) -> a1.vars ++ a2.vars
    BExpr(b1, _, b2) -> b1.vars ++ b2.vars
    Not(b0) -> b0.vars
    _ -> [].Set

fun bb/aexps(b: basicBlock): list<aexp>
  match b
    Assign(_, e) -> e.aexps
    BBlock(e) -> e.aexps
    Skip -> []

fun bexps/aexps(b: bexp): list<aexp>
  match b
    RExpr(a1, _, a2) -> a1.aexps ++ a2.aexps
    BExpr(b1, _, b2) -> b1.aexps ++ b2.aexps
    Not(b0) -> b0.aexps
    _ -> []

fun aexp/aexps(a: aexp): list<aexp>
  match a
    AExp(a1, _, a2) -> Cons(a, a1.aexps ++ a2.aexps)
    _ -> [] // a is trivial

fun kill(s: basicBlock, l: list<aexp>): list<aexp>
  match s
    Assign(v) -> 
      l.filter fn(x)
        match x
          AExp() -> !x.vars.contains(v)
          _ -> False
    _ -> []

fun gen(b: basicBlock): list<aexp>
  match b
    Assign(v, a) -> a.aexps.filter(fn(x) !x.vars.contains(v))
    Skip -> []
    BBlock(b) -> b.aexps


fun test-example_2_4()
  example_2_4.show.println
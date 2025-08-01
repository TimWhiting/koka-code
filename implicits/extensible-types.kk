value struct subtype<s0,s1>
  inj: s0 -> s1 // injection
  prj: s1 -> maybe<s0> // projection

value type or<a,b>
  L(a:a)
  R(b:b)

val or/subtype = Subtype(fn(a) L(a), fn(b) match b {L(x) -> Just(x); _ -> Nothing})

fun convert/subtype(.?subtype: subtype<a,b>): subtype<a,or<c,b>>
  Subtype(fn(a) R(inj(a)), fn(b) match b {R(a) -> prj(a); _ -> Nothing})

alias evalue = or<int, or<func, ()>>;
alias term = or<terma, ()> // , or<termf, or<termr, or<terml, or<termt, or<termc, termn>>>>>>;

type terma
  Num(i: int)
  Add(l: term, r: term)

div type func
  Funct(f: some<e> interpm<evalue> -> e interpm<evalue>)

struct interpm<t>
  interp: some<e> t -> e interpm<t>

alias interpc<t> = some<e> (t -> e interpm<evalue>)

fun or/interp(term: or<t1,t2>, ?t1/interp: interpc<t1>, ?t2/interp: interpc<t2>)
  match term
    L(t) -> interp(t)
    R(t) -> interp(t)

fun a/interp(term: terma)
  match term
    Num(x) -> unit-inj(x)
    Add(x, y) ->
      with i <- bind-prj(interp(x))
      with j <- bind-prj(interp(y))
      unit-inj(i + j)

fun unit-inj(a, ?unit, ?inj)
  unit(inj(a))

fun bind-prj(m, k, ?prj, ?bind)
  with a <- bind(m)
  match prj(a)
    Just(x) -> k(x)
    Nothing -> throw("run-time type error")

fun main()
  val x: evalue = (or/subtype.inj)(1) 
  x.show.println

fun test1( x : or<int,()> )
  x.show

fun test1a( x : or<int,()> )
  x.show(?b/show=unit/show)

fun test2( x : or<int,or<string,()>> )
  x.show

fun func/show(f: func)
  ""

fun or/show(or: or<a,b>, ?a/show: a -> string, ?b/show: b -> string): string
  match or
    L(a) -> show(a)
    R(b) -> show(b)
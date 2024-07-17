import std/data/linearmap
import std/data/linearset

fun showA(a: a)
  ""

fun eqA(a: a, b: a)
  False

rec type comp
  Comp(x: (bool) -> pure ((linearMap<(string, int),(linearSet<bool>, list<comp>)>) -> pure linearMap<(string, int),(linearSet<bool>, list<comp>)>))

fun push(nm: (string, int))
  fn (xs: bool)
    fn (s: linearMap<(string, int),(linearSet<bool>, list<comp>)>): pure linearMap<(string, int),(linearSet<bool>, list<comp>)>
      val (xss, ks) = s.lookup(nm).default((LinearSet([]), []))
      if xss.member(xs) then s
      else
        ks.foldl(s.set(nm, (xss.add(xs), ks))) fn(s', Comp(k))
          k(xs)(s')

fun memo(tag: string, f)
  fn(arg: int)
    val nm = (tag, arg)
    fn(k: (bool) -> pure ((linearMap<(string, int),(linearSet<bool>, list<comp>)>) -> pure linearMap<(string, int),(linearSet<bool>, list<comp>)>))
      fn(s: linearMap<(string, int),(linearSet<bool>, list<comp>)>): pure linearMap<(string, int),(linearSet<bool>, list<comp>)>
        match s.lookup(nm)
          Just((xss:linearSet<bool>, ks)) ->
            xss.list.foldl(s.set(nm, (xss, Cons(Comp(k), ks)))) fn(s', xs)
              k(xs)(s')
          Nothing ->
            f(arg)(push(nm))(s.set(nm, (LinearSet([]), [Comp(k)])))

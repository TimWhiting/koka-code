import std/num/random

fun sort(l : list<int>): <div, exn> list<int>
  match l
    Nil -> Nil
    Cons(x, Nil) -> Cons(x, Nil)
    Cons(pivot, rest) ->
      val lesser = filter(rest, fn (it) { it < pivot })
      val greater = filter(rest, fn (it) { it >= pivot })
      sort(lesser) ++ Cons(pivot, sort(greater))

fun sort2(l : list<int>): <div, exn> list<int>
  match l
    Nil -> Nil
    Cons(x, Nil) -> Cons(x, Nil)
    Cons(pivot, rest) ->
      val (lesser, greater) = partition(rest, fn (it) { it < pivot })
      sort(lesser) ++ Cons(pivot, sort(greater))


inline fun part(o: list<int>, l: list<int>, e: list<int>, g: list<int>, y: list<int>, x: int): <exn, div> list<int>
  match o
    Nil -> sort3(l, e ++ sort3(g, y))
    Cons(z, zs) -> if (z > x) then part(zs, l, e, Cons(z, g), y, x)
                  else if (z < x) then part(zs, Cons(z, l), e, g, y, x)
                  else part(zs, l, Cons(z, e), g, y, x) 

fun sort3(l : list<int>, acc: list<int>): <div, exn> list<int>
  match l
    Nil -> acc
    Cons(x, Nil) -> Cons(x, acc)
    Cons(pivot, rest) -> part(rest, Nil, Cons(pivot, Nil), Nil, acc, pivot)

fun merge(l1: list<int>, l2: list<int>): <div> list<int>
  match l1
    Nil -> l2
    Cons(x, Nil) -> 
      match l2
        Nil -> Nil
        Cons(y, Nil) -> if (x < y) then Cons(x, Cons(y, Nil)) else Cons(y, Cons(x, Nil))
        Cons(y, ys) -> if (x < y) then Cons(x, Cons(y, ys)) else Cons(y, merge(Cons(x, Nil), ys))
    Cons(x, xs) -> 
      match l2
        Nil -> l1
        Cons(y, Nil) -> if (x < y) then Cons(x, merge(xs, Cons(y, Nil))) else Cons(y, merge(Cons(x, xs), Nil))
        Cons(y, ys) -> if (x < y) then Cons(x, merge(xs, Cons(y, ys))) else Cons(y, merge(Cons(x, xs), ys))

fun mergesort(xs: list<int>)
  fun ms(l: list<int>, len: int)
    match l
      Nil -> l
      Cons(_, Nil) -> l
      Cons(x, Cons(y, Nil)) -> if (x < y) then Cons(x, Cons(y, Nil)) else Cons(y, Cons(x, Nil))
      Cons(_, _) ->
        val newLen = len / 2 + 1
        // newLen.show.println()
        val (l1, l2) = l.split(newLen)
        merge(ms(l1, newLen), ms(l2, newLen))
  xs.ms(xs.length)

      
fun genlist(): <div, random> list<int>
  fold-int(0, 10000, Nil) fn (i, t)
    Cons(random-int(), t)

fun main(): <pure, random, console> ()
  fold-int(0, 100, ()) fn(k, _) 
    genlist().mergesort()
    ()
    // 10.show.println()
    // l.show.println()

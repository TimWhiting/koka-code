
import std/os/env

// ------------------------------------------------------------
// ---------------------BEGIN dequeue--------------------------
// ------------------------------------------------------------

import std/core/list

pub struct dequeue<a>( front: list<a>, frontSize: int, rear: list<a>, rearSize: int );

fun listHeadExn<a>( xs: list<a> ): <exn> a
    match xs
        Cons( x, _ ) -> x
        Nil -> throw("Empty list")
        

pub fun emptyQueue<a>(): dequeue<a>
    Dequeue( Nil, 0, Nil, 0 )

pub fun isEmptyQueue<a>( q: dequeue<a> ): bool
    q.frontSize == 0 && q.rearSize == 0

pub fun size<a>( q: dequeue<a> ): int
    q.frontSize + q.rearSize

pub fun first<a>( q: dequeue<a> ): <exn> a
    if ( q.frontSize == 0 && q.rearSize == 1) then
        listHeadExn( q.rear )
    else
        listHeadExn( q.front )

pub fun last<a>( Dequeue(f, fs, r, rs): dequeue<a> ): <exn> a
    if ( fs == 1 && rs == 0) then
        listHeadExn( f )
    else
        listHeadExn( r )

pub fun check<a>( q : dequeue<a> ): dequeue<a>
    match q
        Dequeue(f, fs, r, rs) ->
            val c = 4
            val size1 = (fs + rs) / 2
            val size2 = (fs + rs) - size1
            if ( fs > c * rs + 1 ) then
                val front = f.take( size1 )
                val rear = r ++ f.drop( size1 ).reverse()
                Dequeue( front, size1, rear, size2 )
            else if ( rs > c * fs + 1 ) then
                val front = f ++ r.drop( size1 ).reverse()
                val rear = r.take( size1 )
                Dequeue( front, size2, rear, size1 )
            else
                q

pub fun pushFront<a>( q: dequeue<a>, el : a ): dequeue<a>
    match q
        Dequeue(f, fs, r, rs) ->
            Dequeue( Cons( el, f ), fs + 1, r, rs ).check()

pub fun popFront<a>( q: dequeue<a> ): <exn> (a, dequeue<a>)
    match q
        Dequeue( Nil, _, Cons(x, Nil), _ ) ->
            (x, emptyQueue())
        Dequeue( Nil, _, _, _ ) ->
            throw("Empty queue")
        Dequeue( Cons(x, rest), fs, r, rs ) ->
            (x, Dequeue( rest, fs - 1, r, rs ).check())

pub fun pushBack<a>( q: dequeue<a>, el : a ): dequeue<a>
    match q
        Dequeue(f, fs, r, rs) ->
            Dequeue( f, fs, Cons( el, r ), rs + 1 ).check()

pub fun popBack<a>( q: dequeue<a> ): <exn> (a, dequeue<a>)
    match q
        Dequeue( Cons(x, Nil), _, Nil, _ ) ->
            (x, emptyQueue())
        Dequeue( _, _, Nil, _ ) ->
            throw("Empty queue")
        Dequeue( f, fs, Cons(x, rest), rs ) ->
            (x, Dequeue( f, fs, rest, rs - 1 ).check())

// ------------------------------------------------------------
// ---------------------END dequeue----------------------------
// ------------------------------------------------------------

effect tick
  fun tick(): ()

rec effect process
   ctl yield(): ()
   ctl fork(g: () -> <process, div, exn, st<global>> ()): ()

fun scheduler(f)
  val q: ref<global, dequeue<() -> <div,st<global>|e> ()>> = ref(emptyQueue())

  fun spawn(f1)
    with handler
      raw ctl yield()
        q := (!q).pushBack(fn() rcontext.resume(()))
      raw ctl fork(g)
        q := (!q).pushBack(fn() rcontext.resume(()))
        spawn(g)
    f1()

  fun driver(): <pure,st<global>|e> ()
    val res = (!q).popFront()
    q := snd(res)
    mask<exn>{fst(res)()}
    driver()

  spawn(f)
  with handler
    final ctl throw-exn(err) ()
  driver()

fun job(): <process, pure> ()
  yield()
  
fun jobs(n_jobs: int): <process, tick, pure> ()
  var i: int := 0;
  while {i < n_jobs}
    fork(job)
    tick()
    i := i + 1

fun run(n_jobs : int)
  var c := 0
  with handler
    fun tick() c := c + 1
  scheduler(fn () jobs(n_jobs))
  c

fun repeat(n_jobs : int)
  fun step(i: int, acc: int)
    if i == 0 then
      acc
    else 
      val r: int = run(n_jobs)
      step(i - 1, acc + r)
  step(1, 0)


pub fun main()
  val n = get-args().head("").parse-int().default(5)
  val r = repeat(n)
  println(r)
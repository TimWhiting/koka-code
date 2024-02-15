import std/core/unsafe

pub fun updateOrPush(v: vector<a>, pred: (a) -> e bool, update: (maybe<a>) -> a): e vector<a>
  val updated = v.foreach-while-indexed(fn (i,e) if pred(e) then Just(unsafe-assign(v,i.ssize_t,update(Just(e)))) else Nothing).is-just
  if !updated then
    v.push(update(Nothing))
  else
    v

pub fun push(v: vector<a>, a: a): vector<a>
  val w = unsafe-vector((v.length + 1).ssize_t)
  v.foreach-indexed fn(i,x)
    if i == v.length then
      unsafe-assign(w,i.ssize_t,a)
    else
      unsafe-assign(w,i.ssize_t,x)
  w

pub fun map-indexed( v : vector<a>, f : (int, a) -> e b ) : e vector<b>
  val w = unsafe-vector(v.length.ssize_t)
  v.foreach-indexed fn(i,x)
    unsafe-assign(w,i.ssize_t,f(i,x))
  w

// Invoke a function `f` for each element in a vector `v`.
// If `f` returns `Just`, the iteration is stopped early and the result is returned.
pub fun foreach-while-indexed( v : vector<a>, f : (int, a) -> e maybe<b> ) : e maybe<b>
  for-while( 0, v.length.dec ) fn(i)
    f(i, unsafe-total{v[i]})

inline extern unsafe-vector : forall<a> ( n : ssize_t ) -> total vector<a>
  c  inline "kk_vector_alloc_uninit(#1,NULL,kk_context())"
  cs inline "(new ##1[#1])"
  js inline "Array(#1)"

inline extern unsafe-assign : forall<a> ( v : vector<a>, i : ssize_t, x : a ) -> total ()
  c "kk_vector_unsafe_assign"
  cs inline "(#1)[#2] = #3"
  js inline "(#1)[#2] = #3"
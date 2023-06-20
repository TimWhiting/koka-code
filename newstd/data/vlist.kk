
import std/num/random

pub inline extern unsafe-assign: forall<a> (v: vector<a>, i: ssize_t, x : a) -> <> () {
  c "kk_vector_unsafe_assign"
}

struct vList
  offset: int
  size: int
  lastAssign: int
  previous: maybe<vList>
  values: vector<int>

fun cons(l: vList, n: int): pure vList
  if l.offset == l.size then
    val newSize = l.size*2
    val newVec = vector(newSize, 0)
    newVec.unsafe-assign(0.ssize_t, n)
    // ("biggifying " ++ newSize.show).println()
    VList(offset=0, size=newSize, lastAssign= -1, previous=Just(l), values=newVec)
  else if l.offset - 1 != l.lastAssign then 
    val newVec = vector(4, 0)
    newVec.unsafe-assign(0.ssize_t, n)
    VList(offset=0, size=4, lastAssign= -1, previous=Just(l), values=newVec)
  else
    trace("Update")
    val oldOffset = l.offset
    val newIdx = oldOffset + 1
    l.values.unsafe-assign(l.offset.ssize_t, n)
    trace("Return")
    VList(offset=newIdx, lastAssign=oldOffset, previous=l.previous, size=l.size, values=l.values)

fun show(l: vList): pure string
  var x := ""
  for(0, l.offset - 1) fn(i)
    val v = l.values[i]
    x := x ++ v.show ++ ","
  match l.previous
    Nothing -> x
    Just(l2) -> x ++ l2.show

fun test()
  var l := ref(VList(offset=0, size=4, lastAssign= -1, previous=Nothing, values=vector(4, 0)))
  var i := 0
  repeat(100)
    trace(i.show)
    (!l).show.println()
    val x = (!l).cons(i)
    trace("Consed")
    l.set(x)
    i := i + 1
  (!l).show.println()
  "Finished".println()
  ()

fun main()
  test()

import std/num/random

struct vList
  offset: int
  size: int
  lastAssign: int
  previous: maybe<vList>
  values: vector<int>

fun cons(l: vList, n: int): <console, exn> vList
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
    val oldVec = l.values
    val newIdx = l.offset + 1
    oldVec.unsafe-assign(l.offset.ssize_t, n)
    VList(offset=newIdx, size=l.size, lastAssign=l.offset, previous=l.previous, values=oldVec)

fun show(l: vList): <console, exn, div> string
  var x := ""
  for(0, l.offset - 1) fn(i)
    val v = l.values[l.offset - i - 1]
    x := x ++ v.show ++ ","
  match l.previous
    Nothing -> x
    Just(l2) -> x ++ l2.show

fun test()
  val l = ref(VList(offset=0, size=4, lastAssign= -1, previous=Nothing, values=vector(4, 0)))
  val i = ref(0)
  repeat(100)
    l := (!l).cons(!i)
    i := !i + 1
  (!l).show.println()
  "Finished".println()
  ()

fun main()
  test()
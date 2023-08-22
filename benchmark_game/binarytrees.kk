import std/os/env
import std/num/int32

type tree
  Node(left: tree, right: tree)
  Leaf

fun bottomUpTree(i: int32)
  if i > 0.int32 then
    Node(bottomUpTree(i - 1.int32), bottomUpTree(i - 1.int32))
  else
    Node(Leaf, Leaf)

fun check(tree: tree): div int32
  match tree
    Node(Leaf) -> 1.int32 // Should take care of the Leaf case
    Node(left, right) -> 1.int32 + left.check + right.check
    Leaf -> 0.int32

fun main()
  val n = get-args()[0].default("10").parse-int.unjust
  val minDepth = 4
  val maxDepth = max(minDepth + 2, n)
  val stretchDepth = maxDepth + 1
  println("stretch tree of depth " ++ stretchDepth.show ++ "\t check: " ++ bottomUpTree(stretchDepth.int32).check.show)
  val longLivedTree = bottomUpTree(maxDepth.int32)
  list(minDepth, maxDepth, 2).foreach fn(i)
    val iterations = pow(2, maxDepth - i + minDepth)
    var result := 0.int32
    for(0, iterations - 1) fn(_)
      result := result + bottomUpTree(i.int32).check
    println(iterations.show ++ "\t trees of depth " ++ i.show ++ "\t check: " ++ result.show)
  println("long lived tree of depth " ++ maxDepth.show ++ "\t check: " ++ longLivedTree.check.show)
  
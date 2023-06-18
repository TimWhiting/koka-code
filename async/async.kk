import std/num/random
import std/async
import std/sys/dom

fun main()
  wait(random-float64()*2.0)
  print("Hello, world!\n")
  wait(random-float64()*3.0)
  print("Hi there\n")
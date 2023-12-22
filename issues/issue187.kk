import std/num/int32
import std/time/timer

struct test-config {
    testsize : int
    max-rand-number : int32
}

fun print-test-config(tc) {
    println("Heapsorting " ++ show(tc.testsize) ++ " integers in the range [0, " ++ show(tc.max-rand-number) ++ "):")
}

pub fun raise(s) { throw-exn(Exception(s, ExnError)) }

fun main() {
    val tcs = [ Test-config(    1000, 10000.int32)
              , Test-config(   10000, 100000.int32)
              , Test-config(  100000, 10000000.int32)
              , Test-config( 1000000, 100000000.int32)
              , Test-config(10000000, 1000000000.int32)]

    tcs.map(fn(tc) {
        print-test-config(tc)
        print-elapsed(fn() { if(5 == 2 + 2) { raise("what year is it again?") } else { () } }, "")
        if(tc.testsize <= 100000) { [] } else { [] }
        ()
    })
    ()
}
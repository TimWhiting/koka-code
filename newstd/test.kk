/*----------------------------------------------------------------------------
   Copyright 2024 Tim Whiting

   Licensed under the Apache License, Version 2.0 ("The License"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/

// The test effect
effect test
  ctl test-expect(v: expect-value<a>): a;

// An expected value for a test
struct expect-value<a>
  run-value: error<a> // The value of the computation when run
  expect-value: a // The expected value
  details: maybe<string> // An additional error message providing context of the expectation
  location: string // The line where the expectation was made
  eq: (a,a) -> pure bool // The equality function for the value
  show: (a) -> pure string; // The show function for the value

// Expects a computation to return a value
//
// The expected type must have an `(==)` function as well as a `show` function defined for it
fun expect(expected: a, run: () -> <exn,test|e> a, details: string = "", ?(==): (a,a) -> pure bool, ?show: (a) -> pure string, ?kk-line: string, ?kk-module: string): <test|e> ()
  val res = try({run()})
  test-expect(Expect-value(res, expected, if details == "" then Nothing else Just(details), ?kk-module ++ ":" ++ ?kk-line, (==), show))
  ()

// Runs a test function and prints the first failure including details or "Passed" if all expectations pass in the test
fun test(name: string, f: () -> <test,console,pure|e> (), ?kk-module: string, ?kk-line: string): <console,pure|e> ()
  print("Test(" ++ ?kk-module ++ ":" ++ ?kk-line ++ "): " ++ name ++ " ... ")
  with handler
    ctl test-expect(v)
      val Expect-value(a, b, err, location, eq, showa) = v
      match a
        Error(e) ->
          println("\n  Expect(" ++ location ++ ") == " ++ b.showa ++ ": threw an exception: " ++ e.exn/show ++ err.map(fn(e1) "\n    Details: " ++ e1).default(""))
        Ok(a') -> 
          if a'.eq(b) then
            resume(a')
          else
            println("\n  Expect(" ++ location ++ ") == " ++ b.showa ++ ": but got: " ++ a'.showa ++ err.map(fn(e) "\n    Details: " ++ e).default(""))
    return(x)
      println("Passed!")
  f()

// Some simple examples
fun test-tests()
  test("Returns 1")
    expect(1) fn() 1
  test("Wrong expect")
    expect(1) fn() 2
  test("Additional info")
    expect(1, details="Really expected 1 because I proved it!") fn()
      throw("Some error somewhere")
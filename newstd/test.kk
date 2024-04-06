effect test
  ctl test-expect(v: expect-value<a>): a

struct expect-value<a>
  run-value: error<a>
  expect-value: a
  error: maybe<string>
  line: string
  eq: (a,a) -> pure bool
  show: (a) -> pure string;

fun expect(run: () -> <exn,test|e> a, b: a, error: string = "", ?(==): (a,a) -> pure bool, ?show: (a) -> pure string, ?kk-line: string): <test|e> ()
  val res = try({run()})
  test-expect(Expect-value(res, b, if error == "" then Nothing else Just(error), ?kk-line, (==), show))
  ()

fun test(name: string, f: () -> <test,console,pure|e> (), ?kk-module: string, ?kk-line: string): <console,pure|e> ()
  print("Test(" ++ ?kk-module ++ ":" ++ ?kk-line ++ "):" ++ name ++ " ... ")
  with handler
    ctl test-expect(v)
      val Expect-value(a, b, err, line, eq, showa) = v
      match a
        Error(e) ->
          println("\n\tException: " ++ e.exn/show ++ " in expect " ++ line)
        Ok(a') -> 
          if a'.eq(b) then
            resume(a')
          else
            println("\n\tAt line " ++ line ++ " expected: " ++ b.showa ++ ", got: " ++ a'.showa ++ err.map(fn(e) "\n\t: " ++ e).default(""))
    return(x)
      println("Passed!")
  f()

fun main()
  test("Returns 1")
    expect({1}, 1)
  test("Wrong expect")
    expect({2}, 1)
// Functions have an implicit return for the last statement in the body
fun process(s: string)
  "Hello " ++ s

fun test1()
  // Universal function call syntax (argument before the dot)
  "World!".process.println
  // Same as
  println(process("World!"))

fun createAddN(n: int)
  fn(x)
    x + n
  // Returns a function that adds n to it's argument

fun test2()
  val add5 = createAddN(5)
  add5(10).println
  // Same as
  println(createAddN(5)(10))

fun sum(xs: list<int>, f: (int) -> int)
  match xs
    Cons(x, xs') -> f(x) + sum(xs', f)
    Nil -> 0

fun test3()
  val xs = [0, 1, 2, 3]
  sum(xs, fn(x) x*x).println
  // Same as closure after the closing braces with it's body indented
  val result = sum(xs) fn(x)
    x*x
    // Makes it easier to read longer bodies
  result.println


// Inlining
fun apply(f)
  fn(x)
    f(x)

fun main()
  apply(fn(y) y + 1)(42) + apply(fn(z) z + 1)(35)



// Handlers
effect<a> ctl yield( item : a ) : ()

fun iterate(xs : list<a> ) : yield<a> () 
  match xs
    Cons(x,xx) -> 
      yield(x)
      iterate(xx)
    Nil -> ()

fun nonlinear/main()
  with handler
    ctl yield(a)
      if a == 2 then 
        print("Found a 2!")
        // Do not resume
      else
        println(a)
        resume(())
  [0, 1, 2, 3].iterate

fun linear/main()
  with handler
    ctl yield(a)
      if a == 2 then 
        print("Found a 2!")
        resume(())
      else
        println(a)
        resume(())
  [0, 1, 2, 3].iterate

// fold over the integers between [`start`,`end`] (inclusive).
// fun x/fold( start : int, end : int, init : a, f : (int,a) -> e a ) : e a
//   if start >= end then init else
//     val x = f(start,init)
//     x/fold(unsafe-decreasing(start + 1), end, x, f)

// Computes the number of pythagorean triples such that x < n/3, y < n/2, and z < n/2
fun pyth(n : int): int
  fold(1, n/3, 0) fn(x, xcount) 
    // 1 < x < 30/3
    val xx = x*x // 1^2 < xx < (30/3)^2        
    fold(x.inc, n/2, xcount) fn(y, ycount)  
      // x+1 < y < 30/2  
      val yy = y*y // 1^2+1 < yy < (30/2)^2
      fold-while(y.inc, n/2, ycount) fn(z, zcount)
        // y + 1 < z < 30/2
        val zz = z*z // (1^2+1)^2+1 < zz < (30/2)^2
        // xx+yy < 2*(30/2)^2
        if (xx+yy == zz) then Just(zcount + 1)  
        elif (xx+yy >= zz) && (x+y+z <= n) then Just(zcount)
        else Nothing

fun int/main()
  pyth(30).println
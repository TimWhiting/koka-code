effect <a> ctl yield( item : a ) : ()
  
fun iterate(xs : list<a>) : yield<a> ()
  match xs
    Cons(x, xx) ->
      yield(x)
      iterate(xx)
    Nil -> ()

fun main()
  with handler
    ctl yield(a)
      if a == 2 then
        print(" Found a 2! ")
        resume(())
      else
        println(a)
        resume(())
  [0, 1, 2, 3].iterate
pub fun take-exn(i : () -> exn int) : exn int 
  i()
pub fun get() : e int 
  42

pub fun main()
  val f  :some<e> () -> e int = get
  val str = f().show
  println(str)
  take-exn(f)
  ()
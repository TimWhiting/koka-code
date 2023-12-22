alias elem = int

fun merge(as_ : list<elem>, bs_ : list<elem>) : <exn,div> list<elem> {
    match(as_, bs_) {
        (Cons(a, as'), Cons(b, bs')) {
            if(a > b) then Cons(b, merge(as_, bs'))
            else Cons(a, merge(as', bs_))
        }
        (Nil, _) -> bs_
        (_, Nil) -> as_
    }
}

fun main()
  println("Fixed?")
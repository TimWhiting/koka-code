
alias elem = int

fun sequences(xs : list<elem>) {
    match(xs) {
        Cons(a, Cons(b, xs)) {
            if(a > b) then descending(b, [a], xs)
            else ascending(b, (fn(x) { Cons(a, x) }), xs)
        }
        _ -> [xs]
    }
}

fun descending(a : elem, as_, bs) {
    match(bs) {
        Cons(b, bs) | a > b -> descending(b, Cons(a, as_), bs)
        _ -> Cons(Cons(a, as_), sequences(bs))
    }
}

fun ascending(a : elem, as_, bs) {
    match(bs) {
        Cons(b, bs) | !(a > b) -> ascending(b, fn(ys) { as_(Cons(a, ys)) }, bs)
        _ -> Cons(as_([a]), sequences(bs))
    }
}

fun main()
  "".println
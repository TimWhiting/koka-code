rec type spooky {
    Spooky{ spook : spooky -> int }
}

fun spookMe(s : spooky) : <> int {
    match(s) {
        Spooky(f) -> f(s)
    }
}

fun loop() : <> int { // no div effect!
    spookMe(Spooky(spookMe))
}

fun main() {
    println(loop())
}
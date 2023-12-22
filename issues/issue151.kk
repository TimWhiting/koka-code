
type pipe<e> {
  PipeM { action : () -> e pipe<e> }
}

fun unconsM(p : pipe<<div|e>>) : <div|e> pipe<<div|e>> {
  match(p) {
    PipeM(mp) -> { val p = mp(); unconsM(p) }
  }
}

type benchmark<e> {
    Bench(f : () -> e ())
    BGroup(bs : list<benchmark<e>>)
}

fun run-benchmarks(b : benchmark<<ndet|e>>) : <ndet|e> list<int> {
    match(b) {
        BGroup(bs) {
            bs.map(fn(b) { run-benchmarks(b) }).concat
        }
        Bench(f) {
            f()
            [0]
        }
    }
}

fun main()
  println("")
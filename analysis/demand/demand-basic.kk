import analysis/cps/sexpr

fun main()
  val pr = parseProgramFromString("(lambda (x) x)")
  pr.show.println
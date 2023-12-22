fun ok() : int {
  val five = Just(5)

  match (five) {
    Just(v) -> {
      var a := Nil   // in branch
      return v
    }

    _ -> ()
  }

  7
}

fun main() {
  val v = ok()
  v
}
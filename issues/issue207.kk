fun ppr ( d: float64 ): string {
  match (d) {
    0.0 -> "Can match on 0.0"
    _ -> d.show
  }
}

value type dm { con DM{ deg: int; min: float64 } }

fun ppr ( dm: dm ): string {
  match (dm) {
    //DM(_deg, 0.0) -> "deg-0.0"
    DM(0, _min) -> "0-min"
    DM(_deg, _min) -> "deg-min"
  } 
}
fun test()
  "".println
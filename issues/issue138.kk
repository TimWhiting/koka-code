fun show-a-few-ints(): string {
  val x = 42
  val y = -1
  1.show ++ " " ++ 2.show ++ " " ++ 3.show
    ++ " " ++ 4.show ++ " " ++ 5.show
    ++ " " ++ x.show ++ " " ++ y.show
}
pub fun main() {
  println("A few numbers: " ++ show-a-few-ints())
}
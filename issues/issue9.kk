module issue9

import issue9b

type foo {
  Foo
}

fun to-int(x: foo): int {
  match (x) {
    Foo -> 1
  }
}
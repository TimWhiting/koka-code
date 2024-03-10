fun (==)(m1: maybe<a>, m2: maybe<a>, ?(==): (a, a) -> e bool): e bool
  match (m1, m2)
    (Just(m1'), Just(m2')) -> m1' == m2'
    (Nothing, Nothing) -> True
    _ -> False

fun and(l: list<bool>): bool
  match l
    Nil -> True
    Cons(True, l') -> l'.and
    Cons(False) -> False

fun is-prefix-of(s1: string, s2: string): bool
  s2.starts-with(s1).bool

fun to-upper(c: char): char
  c.string.to-upper.head-char.default(c)
  
fun to-lower(c: char): char
  c.string.to-lower.head-char.default(c)
fun show(m: maybe<a>, showA: (a) -> e string): e string
  match m
    Just(m') -> "Just(" ++ showA(m') ++ ")"
    Nothing -> "Nothing"
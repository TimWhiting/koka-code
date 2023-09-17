fun show(m: maybe<a>, showA: (a) -> e string): e string
  match m
    Just(a) -> "Just(" ++ showA(a) ++ ")"
    Nothing -> "Nothing"

pub fun show-list2( xs : list<a>, show-elem : (a) -> e string ) : e string
  "[" ++ xs.map(show-elem).join(",") ++ "]"
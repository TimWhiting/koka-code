struct queue<q,a>
  q-empty: q<a>
  q-is-empty: (q<a>) -> bool
  q-snoc: (q<a>, a) -> q<a>
  q-head: (q<a>) -> emptyqueue a
  q-tail: (q<a>) -> emptyqueue q<a>;

effect emptyqueue
  final ctl err-empty(): a;

// Batched Queue
value struct bQ<a>
  front: list<a>
  back: list<a>

fun bq/check(f: list<a>, r: list<a>): bQ<a>
  match f
    Nil -> BQ(r.reverse, [])
    _ -> BQ(f, r)

val batched/queue = Queue(
  BQ([], []),
  fn(BQ(f,_)) f.is-empty,
  fn(BQ(f,r), x) bq/check(f, Cons(x,r)),
  fn(bq)
    match bq
      BQ([], _) -> err-empty()
      BQ(Cons(x,_), _) -> x
  ,
  fn(bq)
    match bq
      BQ([], _) -> err-empty()
      BQ(Cons(_,f), r) -> bq/check(f,r)
)


// Bankers Queue
value struct baQ<a>
  lenf: int
  f: list<a>
  lenr: int
  r: list<a>

fun baq/check(lenf: int, f: list<a>, lenr: int, r: list<a>): baQ<a>
  if lenr <= lenf
  then BaQ(lenf, f, lenr, r)
  else BaQ(lenf + lenr, f ++ r.reverse, 0, [])

val bankers/queue = Queue(
  BaQ(0, [], 0, []),
  fn(BaQ(lenf,_,_,_)) lenf == 0,
  fn(BaQ(lenf,f,lenr,r), x) baq/check(lenf, f, lenr + 1, Cons(x,r)),
  fn(bq)
    match bq
      BaQ(_, Nil, _, _) -> err-empty()
      BaQ(_, Cons(x,_), _, _) -> x
  ,
  fn(bq)
    match bq
      BaQ(_, Nil, _, _) -> err-empty()
      BaQ(lenf, Cons(_,f), lenr, r) -> baq/check(lenf - 1, f, lenr, r)
)

fun snoc(q: q<a>, x: a, ?this/queue: queue<q,a>): q<a>
  (this/queue.q-snoc)(q,x)

fun head(q: q<a>, ?this/queue:queue<q,a>): emptyqueue a
  (this/queue.q-head)(q)

fun tail(q: q<a>, ?this/queue:queue<q,a>): emptyqueue q<a>
  (this/queue.q-tail)(q)

fun queue/empty(?q:queue<q,a>): q<a>
  q.q-empty

fun queue/is-empty(q: q<a>, ?this/queue:queue<q,a>): bool
  (this/queue.q-is-empty)(q)

fun queue/list(q:q<a>, ?this/queue:queue<q,a>): <div> list<a>
  with final ctl err-empty() Nil
  Cons(q.head, queue/list(q.tail))

fun main()
  val q = queue/empty(bankers/queue)
  q.snoc(1).queue/list.list/show()
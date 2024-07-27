struct queue<q,a>
  q-empty: q<a>
  q-is-empty: (q<a>) -> bool
  q-snoc: (q<a>, a) -> q<a>
  q-head: (q<a>) -> emptyqueue a
  q-tail: (q<a>) -> emptyqueue q<a>;

effect emptyqueue
  final ctl err-empty(): a;

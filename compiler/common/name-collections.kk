import newstd/data/linearmap
import newstd/data/linearset
import compiler/common/name
import compiler/common/failure
import compiler/platform/config

alias name-map<a> = linearMap<name, a>;

fun find(m: name-map<a>, n: name): <div,exn> a
  match m.maybeGet(n)
    Just(x) -> x
    _ -> throw("common/name-map.find: could not find: " ++ n.show)

alias nameSet = linearSet<name>;
val namesEmpty = linearSet([], fn(a:name, b:name) a == b, fn(a:name) a.show)

alias qname-map<a> = linearMap<name,list<(name,a)>>;

type lookup<a>
  Found(name: (name, a))
  Ambiguous(names: list<name>)
  NotFound

fun (==)(l1: list<a>, l2: list<a>, eqA: (a, a) -> e bool): e bool
  match (l1, l2)
    (Nil, Nil) -> True
    (Cons(x, xs), Cons(y, ys)) -> eqA(x, y) && (==)(xs, ys, eqA)
    _ -> False

fun eqNameList(l1: list<(name,a)>, l2: list<(name,a)>, eqA: (a, a) -> e bool): e bool
  match (l1, l2)
    (Nil, Nil) -> True
    (Cons((n1, x), xs), Cons((n2, y), ys)) -> n1 == n2 && eqA(x, y) && eqNameList(xs, ys, eqA)
    _ -> False

fun showNameList(l: list<(name,a)>, showA: (a) -> e string): e string
  l.show-list(fn((n, a)) "(" ++ n.show ++ ", " ++ a.showA ++ ")")

fun single(n: name, a: a, eqA: (a, a) -> <div|e> bool, showA: (a) -> <div|e> string): qname-map<a>
  linearMap([(n.unqualify, [(n, a)])], fn(k1:name, k2) k1 == k2, fn(v1, v2) eqNameList(v1, v2, eqA), fn(n') n'.show, fn(l) l.showNameList(showA))

fun insertName(m: qname-map<a>, n: name, a: a): <compFlags,exn> qname-map<a>
  m.update(n.unqualify, Cons((n, a), Nil)) fn(xs, ys)
    safeCombine("insert", xs, ys)

fun fromList(l: list<(name,a)>, eqA: (a, a) -> <div|e> bool, showA: (a) -> <div|e> string): <compFlags,pure> qname-map<a>
  l.foldl(linearMap([], fn(k1:name, k2) k1 == k2, fn(v1, v2) eqNameList(v1, v2, eqA), fn(n) n.show, fn(l') l'.showNameList(showA))) fn(qm, (name, x))
    qm.insertName(name, x)

fun safeCombine(s: string, xs: list<(name,a)>, ys: list<(name,a)>): <compFlags,exn> list<(name,a)>
  if xs.any(fn(x) -> ys.any(fn(y) -> y.fst == x.fst)) then
    fail("common/name-collections " ++ s ++ ": overlapping names: " ++ xs.map(fn(x) -> x.fst.show).show ++ ys.map(fn(y) -> y.fst.show).show)
  xs ++ ys

// Lookup a fully qualified name
fun lookupQ(m: qname-map<a>, n: name): maybe<a>
  match m.maybeGet(n.unqualify)
    Just(xs) -> xs.lookup(fn(o) o == n)
    _ -> Nothing

// Lookup a potentially unqualified name within a module context. 
// (The module context is ignored if a qualified name is looked up)
fun lookup(m: qname-map<a>, c: name, name: name): lookup<a>
  match m.maybeGet(name.unqualify)
    Just(Cons((qname,x), _)) | !name.isQualified -> Found((qname, x))
    Just(xs) ->
      val qname = if name.isQualified then name else c.qualify(name)
      match xs.filter(fn(p) -> p.fst == qname)
        Cons((realname, x), _) -> Found((realname, x))
        _ -> Ambiguous(xs.map(fst))
    _ -> NotFound

// fun filterNames(m: qname-map<a>, p: (name) -> bool): qname-map<a>
// TODO: The rest of the name collection functions
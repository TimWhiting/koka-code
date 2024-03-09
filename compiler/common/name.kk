import compiler/lib/pprint
import compiler/common/range
import std/core/undiv
import newstd/core


// | Names defined by the user.
// Uses a hash to speed up comparisions. The hash is constructed
// such that they can be compared too. (h1 > h2 => name1 > name2)
// The hash is case-insensitive, just like comparisions on names.
// Use 'name-case-equal' for case-sensitive comparisions.
//
// Notes:
// - We use `name/local` for the locally qualified name in the module (`int/show`)
// - The stem is the plain name and operators are not parenthesized (`++`)
// - The stem should always be a valid identifier; this means that an operator
//   must keep ending with symbols. When hiding names etc, we can get names like `@temp12-++` for example
// - We assume that users cannot start identifiers with an `@`. (We may in the future allow
//   user identifiers to contain `@` though after the first character.)
// - Plain module names have an empty local qualifier and stem
// - If there is a local qualifier, the stem cannot be empty
struct name
  pub nameModule: string // module name (`std/core`)
  pub hashModule: int
  pub nameLocalQual: string // local qualifier (`int`)
  pub hashLocalQual: int
  pub nameStem: string  // the stem (`show`)
  pub hashStem: int

// names
alias names = list<name>

fun join(m: string, n: string): string
  m ++ "/" ++ n

fun name/local(n: name): string
  join(n.nameLocalQual, n.nameStem)

fun name-case-equal(n1: name, n2: name): bool
  n1.local == n2.local && 
    n1.split-module-name.reverse.zipwith(n2.split-module-name.reverse, (==)).and

fun name-case-equal-prefix-of(n1: name, n2: name): bool
  n1.local.is-prefix-of(n2.local) &&
    n1.split-module-name.reverse.zipwith(n2.split-module-name.reverse, (==)).and

fun name-case-overlap(n1: name, n2: name): bool
  !n1.name-case-equal(n2) && n1.is-same-namespace(n2)
    
fun is-same-namespace(n1: name, n2: name): bool
  match (n1.nameStem.list, n2.nameStem.list)
    (Cons(c, _), Cons(d, _)) -> c.is-upper && d.is-upper
    _ -> True

fun lower/cmp(Name(m1, _, n1, _), Name(m2, _, n2, _)): order
  match cmp(m1.to-lower, m2.to-lower)
    Eq -> cmp(n1.to-lower, n2.to-lower)
    lg -> lg

pub fun name/(==)(n1: name, n2: name): bool
  n1.hashStem == n2.hashStem && n1.hashModule == n2.hashModule && n1.lower/cmp(n2) == Eq

val nameEq = fn(n1: name, n2: name) n1 == n2

fun namelist/(==)(l1: list<name>, l2: list<name>): bool
  match (l1, l2)
    (Nil, Nil) -> True
    (Cons(a, ra), Cons(b, rb)) -> a == b && ra.pretend-decreasing == rb
    _ -> False

pub fun (!=)(n1: name, n2: name): bool
  !(n1 == n2)

pub fun name/cmp(n1: name, n2: name): order
  match n1.hashModule.cmp(n2.hashModule)
    Eq -> 
      match n1.hashStem.cmp(n2.hashStem)
        Eq -> n1.lower/cmp(n2)
        x -> x
    x -> x

fun label-name/cmp(n1: name, n2: name): order
  match n1.hashStem.int/cmp(n2.hashStem)
    Eq -> 
      match n1.nameStem.to-lower.string/cmp(n2.nameStem.to-lower)
        Eq -> 
          match n1.hashModule.int/cmp(n2.hashModule)
            Eq -> n1.nameModule.to-lower.string/cmp(n2.nameModule.to-lower)
            x -> x
        x -> x
    x -> x

val canonical-sep = '@'

fun name/show(Name(m, _, n, _)): string
  val pre = if m == "" then "" else m ++ "/"
  val (mid, _) = match n.list.reverse.span(is-digit)
    (Cons(p, ps), Cons(c, rest)) | (c == canonical-sep) -> (rest.reverse, Cons(c, Cons(p, ps).reverse))
    _ -> (n.list, "".list)
  val rest = match mid
    Cons(c, _) | !(c.is-alpha || c == '_' || c == '(' || c == '@') -> "(" ++ n ++ ")"
    _ -> n
  pre ++ rest

fun show-plain(n: name): string // TODO: better name show
  if n.nameModule.is-empty then n.nameStem else n.nameModule ++ "/" ++ n.nameStem

fun pretty(n: name): doc
  n.name/name/show.text

fun tupled/show(Name(m, _, n, _)): string
  "(" ++ m.show ++ "," ++ n.show ++ ")"

fun tupled/read(s: string): exn name
  val Cons(t1, Cons(t2, _)) = s.split(",") // TODO: Strip parens
  new-qualified(t1, t2)

fun qualified/read(s: string): exn name
  val sl = s.list
  if (sl.take(1).head.default(' ') == '(') then tupled/read(s)
  else
    val (n, m) = sl.reverse.span(fn(c) -> c != '/')
    new-qualified(m.drop(1).reverse.string, n.reverse.string)

// show quotes around the name
fun namequotes/show(n: name): string
  n.name/name/show.string/show

fun new-name(s: string): name
  new-qualified("", s)

fun new-qualified(mod: string, name: string): name
  new-locally-qualified(mod, "", name)

fun new-locally-qualified(m: string, l: string, n: string): name
  Name(m, m.hash, l, l.hash, n, n.hash)

// The hash function:
//  1) can be compared: h1 < h2  => name1 < name2 && h1 > h2 => name1 > name2
//  2) assumes 32 bit integers and no characters in strings >= \x128
//  3) is case in-sensitive (ie. does tolower first)
// The hash is done taking the first 4 characters. This is of course a
// terrible hash but we use it mostly to speed up *comparisions* for the nameMap
fun hash(s: string)
  val sn = (s ++ "____").list.take(4).string.to-lower.list.map(fn (c) { c.int })
  sn.foldl(0, fn(c, h) { h * 256 + c})

val name/nil = "".new-name

fun is-nil(Name(_, _, n, _)): bool
  n == ""

fun qualify(a: name, b: name): name
  match (a, b)
    (Name(m, hm, _, 0, _, 0), Name(_, 0, l, hl, n, hn)) -> Name(m, hm, l, hl, n, hn)
    (Name(m1, _, _, 0, _, 0), name as Name(m2)) | m1 == m2 -> name
    _ ->
      trace("Cannot use qualify on qualified names " ++ a.name/name/show ++ ", " ++ b.name/name/show)
      new-name("")

fun unqualify(Name(_, _,l, hl, n, hn)): name
  Name("", 0, l, hl, n, hn)

fun is-qualified(Name(m)): bool
  m != ""

fun qualifier(Name(m, hm)): name
  Name(m, hm, "", 0, "", 0)

// Module paths
fun split-module-name(n: name): list<name>
  if n.is-qualified then pretend-decreasing(n.qualifier).split-module-name
  else n.name/name/show.split("/").map(fn(s) -> s.new-name)

fun unsplit-module-name(l: list<name>): name
  l.map(fn(n) n.name/name/show).join("/").new-name

fun merge(l1: list<name>, l2: list<name>): list<name>
  match (l1, l2)
    (Cons(m, ms), Cons(n, ns)) -> 
      if m == n && ms.zipwith(ns, fn(i, j) -> i == j).all(fn(i) -> i) then
        Cons(m, ms) ++ ns.drop(ms.length)
      else
        Cons(m, merge(pretend-decreasing(ms), Cons(n, ns)))
    (Cons(m, ms), ns) -> Cons(m, merge(pretend-decreasing(ms), ns))
    (_, ns) -> ns

fun merge-common-path(n1: name, n2: name): name
  val ns = n2.split-module-name
  val ms = n1.split-module-name
  val new = ms.merge(ns).unsplit-module-name
  new

fun is-wildcard(Name(_, _, n, _)): bool
  match n.list
    Cons('_', _) -> True
    Cons('@', Cons('_', _)) -> True
    _ -> False

fun is-constructor-name(Name(_, _, n, _)): bool
  match n.list
    Cons('@', Cons(c, _)) -> c.is-upper || c == '('
    Cons(c, _) -> c.is-upper || c == '('
    _ -> False

fun is-early-bind-name(n: name): bool
  n.is-handle-name || n.is-creator-name

// TODO: Move to std library
fun to-upper(c: char): char
  c.string.to-upper.head-char.default(c)
fun to-lower(c: char): char
  c.string.to-lower.head-char.default(c)

fun to-constructor-name(Name(m, _, n, _)): name
  val nl = n.list
  val new = match nl
    Cons('@', Cons(c, cs)) -> Cons('@', Cons(c.to-upper, cs)) // keep hidden names hidden
    Cons(c, cs) -> Cons(c.to-upper, cs)
    _ -> nl
  m.new-qualified(new.string)

fun to-lowers(l: list<char>): list<char>
    match l
      Cons(c, cs) | c.is-upper -> Cons(c.to-lower, to-lowers(cs))
      _ -> l

fun to-var-name(Name(m, _, n, _)): name 
  val new = match n.list
    Cons('@', cs) -> Cons('@', cs.to-lowers) // keep hidden names hidden
    cs -> cs.to-lowers
  m.new-qualified(new.string)

fun name/starts-with(n: name, s: string): bool
  n.nameStem.starts-with(s).bool

// Various special names
fun new-hidden-name(s: string): name
  new-name("." ++ s)

fun is-hidden(n: name): bool
  match n.nameStem.list
    Cons('@', _) -> True
    _ -> False

fun make-hidden-name(s: string, n: name): name
  val xname = match n.nameStem.list
    Cons('@', cs) -> new-qualified(n.nameModule, cs.string)
    _ -> n
  prepend("." ++ s ++ "-", xname)

fun make-fresh-hidden-name(s: string, n: name, r: range)
  val idFromPos = fn(p) -> "-l" ++ p.line.show ++ "-c" ++ p.col.show
  make-hidden-name(s, postpend(r.start.idFromPos, n))

fun hidden/starts-with(n: name, pre: string): bool
  n.nameStem.starts-with("." ++ pre ++ "-").bool

fun to-unique-name(i: int, n: name): name
  fun insert(l: list<char>): list<char>
    match l
      Cons(c, cs) | c == '\'' || c == '?' -> Cons(c, cs.insert)
      _ -> (i.show ++ l.string).list.reverse
  n.nameModule.new-qualified(n.nameStem.list.reverse.insert.reverse.string)

fun to-hidden-unique-name(i: int, s: string, n: name): name
  if s == "" then
    prepend(".", to-unique-name(i, n))
  else
    val c = n.nameStem.head-char.default(' ')
    val xname = if c.is-alpha || c == '@' then n else n.nameModule.new-qualified("op")
    make-hidden-name(s ++ i.show, xname)

fun new-padding-name(i: int)
  new-hidden-name("padding" ++ i.show)

fun is-padding-name(n: name)
  n.nameStem.starts-with("@padding").is-just

fun is-cctx-name(n: name)
  n.nameStem.starts-with("@cctx").is-just

fun new-field-name(i: int): name
  new-hidden-name("field" ++ i.show)

fun is-field-name(n: name): bool
  n.is-hidden && n.name/name/starts-with("field")

fun new-implicit-typevar-name(i: int): name
  new-hidden-name("t" ++ i.show)

fun is-implicit-typevar-name(n: name): bool
  n.is-hidden && n.name/name/starts-with("t")

fun new-hidden-external-name(n: name): name
  make-hidden-name("extern", n)

fun is-hidden-external-name(n: name): bool
  n.hidden/starts-with("extern")

fun to-implicit-param-name(n: name): name
  prepend("?", n)

fun is-implicit-param-name(n: name): bool
  n.nameStem.starts-with("?").bool

fun plain-implicit-param-name(n: name): name
  if n.is-implicit-param-name then n.nameModule.new-qualified(n.nameStem.slice.drop(1).string)
  else n

fun named-implicit-param-name(pname: name, ename: name): name
  (pname.plain-implicit-param-name.nameStem ++ "," ++ ename.nameStem).new-name.to-implicit-param-name()

fun split-implicit-param-name(n: name): (name, name)
  val (pre, post) = n.plain-implicit-param-name.nameStem.list.span(fn(c) c != ',')
  match post
    Cons(_, ename) | !pre.is-nil -> (pre.string.new-name, ename.string.new-name)
    _ -> (n, n.plain-implicit-param-name)

// Create a constructor creator name from the constructor name.
// Used if special creation functions are used for the constructor.
// in particular for the case of optional arguments.
fun new-creator-name(n: name): name
  make-hidden-name("create", n)

fun is-creator-name(n: name): bool
  n.hidden/starts-with("create")

// Create a handler type name from an effect type name.
fun to-handler-name(n: name): name
  make-hidden-name("hnd", n)

fun is-handler-name(n: name): bool
  n.nameStem.starts-with("@hnd-").bool

// Create an effect type name from an operations type name.
fun from-handler-name(n: name): name
  n.nameModule.new-qualified(n.nameStem.list.drop(5).string)

// Create a handle function name from an effect type name.
fun to-handle-name(n: name): name
  make-hidden-name("handle", n)

fun is-handle-name(n: name): bool
  n.hidden/starts-with("handle")

// Create an operations type name from an effect type name.
fun to-operations-name(n: name): name
  make-hidden-name("ops", n)

// Is this an operations name?
fun is-operations-name(n: name): bool
  n.nameStem.starts-with("@ops-").bool

fun to-op-selector-name(n: name): name
  make-hidden-name("select", n)

// Is this an operations name?
fun is-op-selector-name(n: name): bool
  n.nameStem.starts-with("@select-").bool

//  Create an effect type name from an operations type name.
fun from-op-selector-name(n: name): name
  n.nameModule.new-qualified(n.nameStem.list.drop(8).string)

// Create an effect tag name from an effect type name.
fun to-effect-tag-name(n: name): name
  make-hidden-name("tag", n)

// Create an operation type name from an operation name.
fun to-op-type-name(n: name): name
  make-hidden-name("op", n)

// Create an operation constructor name from an operation name.
fun to-op-con-name(n: name): name
  make-hidden-name("Op", n)

// Create an open tag name from a constructor name in an open type
fun to-open-tag-name(n: name): name
  make-hidden-name("tag", n)

fun is-open-tag-name(n: name): bool
  n.nameStem.starts-with("@tag-").bool

// Create a name for a value operation
fun to-value-operation-name(n: name): name
  make-hidden-name("val", n)

// Is this an name of a value operation?
fun is-value-operation-name(n: name): bool
  n.nameStem.starts-with("@val-").bool

// Create an operation name from a value operation name
fun from-value-operations-name(n: name): name
  n.nameModule.new-qualified(n.nameStem.list.drop(5).string)

fun prepend(s: string, n: name): name
  val sl = s.list
  val new = match n.nameStem.list
    Cons('@', t) -> match sl
      Cons('@', _) -> sl ++ t // Keep hidden names hidden
      _ -> Cons('@', sl ++ t)
    t -> sl ++ t
  new-qualified(n.nameModule, new.string)

fun postpend(s: string, cname: name): name
  val (name, post) = cname.canonical-split
  new-qualified(name.nameModule, name.nameStem ++ s ++ post)

fun canonical-name(n: int, name: name): name
  if n == 0 then name else postpend(canonical-sep.string ++ n.show, name)

fun non-canonical-name(n: name): name
  n.canonical-split.fst

fun canonical-split(n: name): (name, string)
  match n.nameStem.list.reverse.span(is-digit)
    (Cons(p, ps), Cons(c, rest)) | c == canonical-sep -> (new-qualified(n.nameModule, rest.reverse.string), Cons(c, Cons(p, ps).reverse).string)
    _ -> (n, "")

// camel-case to dash-case
fun camel-to-dash(s: string): string
  match s.split-camel
    Cons(x, xs) -> x ++ xs.map(fn(y:string) "-" ++ y.to-lower).join
    _ -> ""

fun split-camel(s: string): list<string>
  fun is-break(c: char): bool
    c.is-alpha || c == '-'
  if s == "" then Nil
  else
    match s.list
      Cons('-', cs) -> pretend-decreasing(cs.string).split-camel
      Cons(c, cs) -> 
        val (pre, post) = cs.span(is-break)
        if post.is-empty then
          val (pre2, post2) = post.span(fn(i) -> i.is-upper)
          if pre2.is-empty || post.is-empty && post2.head.default(' ').is-break then
            Cons(Cons(c, pre2).string, pretend-decreasing(post2.string).split-camel)
          else
            Cons(Cons(c, pre2.init).string, pretend-decreasing(Cons(pre2.last.default(' '), post2).string).split-camel)
        else
          Cons(Cons(c, pre).string, pretend-decreasing(post.string).split-camel)
      Nil -> Nil

// name to file path
fun module-name-to-path(n: name): string
  n.name/name/show.ascii-encode(True)

fun path-to-module-name(p: string): name
  fun decode(s: string): string // TODO: Performance
    val sl = s.list
    match sl
      _ | s.starts-with("_dash_").bool -> "-" ++ decode(pretend-decreasing(sl.drop(6).string))
      Cons('_', Cons('_', t)) -> "_" ++ decode(pretend-decreasing(t.string))
      Cons('_', t) -> "/" ++ decode(pretend-decreasing(t.string))
      Cons('@', t) -> decode(pretend-decreasing(t.string))
      Cons('\\', t) -> "/" ++ decode(pretend-decreasing(t.string))
      Cons(c, t) -> c.string ++ decode(pretend-decreasing(t.string))
      Nil -> ""
  p.decode.list.drop-while(fn(c) -> c == '_' || c == '@' || c == '/').string.new-name

fun ascii-encode(n: string, is-module: bool): string
  fun encode-char(pre: char, c: char, post: char): string
    match c
      '/' | is-module -> "_"
      '-' | !is-module && post.is-alpha-num -> "_"
      '@' | post.is-digit || post == ' ' || pre == ' ' -> "_"
      '_' -> "__"
      '@' -> "_dot_"
      '-' -> "_dash_"
      '/' -> "_fs_"

      '+' -> "_plus_"
      '*' -> "_star_"
      '&' -> "_amp_"
      '~' -> "_tilde_"
      '!' -> "_excl_"
      '@' -> "_at_"
      '#' -> "_hash_"
      '$' -> "_dollar_"
      '%' -> "_perc_"
      '^' -> "_hat_"
      '=' -> "_eq_"
      ':' -> "_colon_"
      '<' -> "_lt_"
      '>' -> "_gt_"
      '[' -> "_lb_"
      ']' -> "_rb_"
      '?' -> "_ques_"
      '\\'-> "_bs_"
      '(' -> "_lp_"
      ')' -> "_rp_"
      ',' -> "_comma_"
      ' ' -> "_space_"
      '\'' -> "_sq_"
      '\"' -> "_dq_"
      '`'  -> "_bq_"
      '{'  -> "_lc_"
      '}'  -> "_rc_"
      '|'  -> "_bar_"
      _ -> "_x" ++ c.int.show-hex(pre="", width=2) ++ "_"

  fun encode-chars2(s: list<char>): list<string>
    match s
      Cons(pre, Cons(c, Cons(post, rest))) -> Cons(encode-char(pre, c, post), encode-chars2(rest))
      Cons(pre, Cons(c, Nil)) -> Cons(encode-char(pre, c, ' '), Nil)
      Cons(pre, Nil) -> Cons(pre.string, Nil)
      Nil -> Nil
  
  fun encode-chars(s: string): string
    encode-chars2((" " ++ s).list).join

  if n.head-char.default(' ').is-alpha-num then
    return n.encode-chars
  match n
    ""      -> "_null_"
    ".<>"   -> "_total_"
    ".<|>"  -> "_extend_"
    ".()"   -> "_unit_"
    ".(,)"  -> "_tuple2_"
    ".(,,)" -> "_tuple3_"
    ".(,,,)"-> "_tuple4_"
    "()"    -> "_Unit_"
    "(,)"   -> "_Tuple2_"
    "(,,)"  -> "_Tuple3_"
    "(,,,)" -> "_Tuple4_"
    "[]"    -> "_index_"
    _ -> n.encode-chars
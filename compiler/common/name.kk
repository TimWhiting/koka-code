//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 7/23/24 Commit: e25043b

import compiler/common/color-scheme
import compiler/common/range
import compiler/common/failure
import compiler/lib/printer
import compiler/lib/pprint
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
  if m == "" then n
  elif n == "" then m
  else m ++ "/" ++ n

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

fun name-case-overlap-prefix-of(n1: name, n2: name): bool
  !n1.name-case-equal-prefix-of(n2) && n1.is-same-namespace(n2)

// Checks whether both names are in the same namespace, ie. constructors or not
fun is-same-namespace(n1: name, n2: name): bool
  n1.is-constructor-name == n2.is-constructor-name

fun lower/cmp(Name(m1, _, l1, _, n1, _): name, Name(m2, _, l2, _, n2, _): name): order
  match cmp(m1.to-lower, m2.to-lower)
    Eq -> match cmp(l1.to-lower, l2.to-lower)
      Eq -> cmp(n1.to-lower, n2.to-lower)
      lg -> lg
    lg -> lg

fun string/cmp-lower(s1: string, s2: string): order
  slice/cmp-lower(s1.slice,s2.slice)

fun slice/cmp-lower(s1: sslice, s2: sslice): order
  match (s1.next, s2.next)
    (Just((c1, r1)), Just((c2, r2))) -> 
      match c1.to-lower.cmp(c2.to-lower)
        Eq -> slice/cmp-lower(r1.pretend-decreasing, r2)
        lg -> lg
    (Just, _) -> Gt
    (_, Just) -> Lt
    (_, _) -> Eq

pub fun name/(==)(n1: name, n2: name): bool
  val eq = n1.hashStem == n2.hashStem && n1.hashModule == n2.hashModule && n1.hashLocalQual == n2.hashLocalQual
  assert("common/name/(==): wrong hashes: " ++ n1.show-fully-explicit ++ 
         " " ++ n2.show-fully-explicit, 
         eq || n1.show-fully-explicit != n2.show-fully-explicit)
  eq && n1.lower/cmp(n2) == Eq

val nameEq = fn(n1: name, n2: name) n1 == n2

pub fun (!=)(n1: name, n2: name): bool
  !(n1 == n2)

pub fun name/cmp(n1: name, n2: name): order
  match n1.hashModule.cmp(n2.hashModule)
    Eq -> match n1.hashLocalQual.cmp(n2.hashLocalQual)
      Eq -> match n1.hashStem.cmp(n2.hashStem)
        Eq -> n1.lower/cmp(n2)
        lg -> lg
      lg -> lg
    lg -> lg

// Effects compare by name first, then by module name for efficiency at runtime
fun label-name/cmp(n1: name, n2: name): order
  match n1.hashStem.int/cmp(n2.hashStem)
    Eq -> match n1.nameStem.cmp-lower(n2.nameStem)
      Eq -> match n1.hashLocalQual.int/cmp(n2.hashLocalQual)
        Eq -> match n1.nameLocalQual.cmp-lower(n2.nameLocalQual)
          Eq -> match n1.hashModule.int/cmp(n2.hashModule)
            Eq -> n1.nameModule.cmp-lower(n2.nameModule)
            lg -> lg
          lg -> lg
        lg -> lg
      lg -> lg
    lg -> lg

fun is-id-char(c: char): bool
  c.is-alpha || c.is-digit || c == '_' || c == '-' || c == '@'

fun is-id-start-char(c: char): bool
  c.is-alpha || c == '_' || c == '@'

fun is-id-end-char(c: char): bool
  c.is-id-char || c == '\''

fun is-symbol-id(s: string): bool
  s != "" && 
    // The default cases shouldn't happen because of the check above
    (s.head-char.map(fn(c) !c.is-id-start-char).default(False) ||
     s.last(1).next.map(fn((c,_)) !c.is-id-end-char).default(False))

fun wrap-id(s: string): string
  if is-symbol-id(s) then "(" ++ s ++ ")" else s

fun name/show-name(Name(m, _, l, _, n, _): name, explicitLocalQualifier: bool): string
  val ln = l.join(n.wrap-id)
  if m == "" then ln 
  elif ln == "" then m
  else m ++ (if explicitLocalQualifier && l != "" then "/#" else "/") ++ ln

fun show-fully-explicit(Name(m, _, l, _, n, _): name): string
  val ln = l.join(n.wrap-id)
  if m == "" then "#" ++ ln
  elif ln == "" then m
  else m ++ "/#" ++ ln

fun show-explicit(n: name): string
  n.show-name(True)

fun show-plain(n: name): string 
  join(n.nameModule, join(n.nameLocalQual, n.nameStem))

fun name/show(n: name): string
  n.show-explicit()

fun pretty(n: name): doc
  n.show.text

fun pretty-name-ex(Name(m, _, l, _, n, _): name, lsep: string, cs: colorScheme): doc // explicit /# if needed
  val ln = join(l, n.wrap-id)
  if m == "" then ln.text
  else 
   (m.text |.| (if ln.is-empty then pprint/empty elif l.is-empty then "/".text else lsep.text)).color(cs.colorModule)
           |.| ln.text
  

fun pretty-name(nm: name, cs: colorScheme): <exn> doc // not explicit /#
  if nm.is-implicit-param-name then "?".text |.| nm.from-implicit-param-name.requalify-locally.pretty-name-ex("/", cs)
  else nm.pretty-name-ex("/", cs)

fun pretty-core-name(nm: name, cs: colorScheme): doc // explicit /# if needed
  nm.pretty-name-ex("/#", cs)

fun show-tupled(Name(m, _, l, _, n, _): name): string
  "(" ++ m ++ "," ++ l ++ "," ++ n ++ ")"

fun tupled/read(s: string): exn name
  val s' = s.slice.drop(1).extend(-1).string // Drop ()
  val Cons(m, Cons(l, Cons(n, Nil))) = s'.split(",")
  new-locally-qualified(m, l, n)

fun qualified/read(s: string): <div,exn> name
  if s.starts-with("(").bool then tupled/read(s)
  else s.read-qualified-name

fun new-name(s: string): name
  new-qualified("", s)

fun new-module-name(s: string): name
  new-qualified(s, "")

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
  if s.is-empty then 0
  else
    val sn = (s ++ "____").list.take(4).string.to-lower.list.map(fn (c) { c.int })
    sn.foldl(0, fn(c, h) { h * 256 + c})

fun name-map-stem(Name(m, hm, l, hl, n, _): name, f: (string) -> e string): e name
  val n' = f(n)
  Name(m, hm, l, hl, n', n'.hash)

fun read-qualified-name(s0: string): <div,exn> name
  if s0.starts-with("?").bool then s0.slice.drop(1).string.read-qualified-name.requalify-locally.to-implicit-param-name
  else
    fun split-qual-id-rev(rs: list<char>): (string, string)
      val (rid, rqual) = rs.span(fn(c) c != '/')
      match rqual
        Cons('/', rs1) -> (rid.string, rs1.string) // qualifier
        _ -> ("", rid.string)
    fun split-id-name-rev(rs: list<char>): <exn> (string, string, string)
      val (rid, rest) = rs.span(fn(c) c != '#')
      match rest
        Cons('#', Cons('/', rs2)) -> // local qualifier
          val (lqual,id) = rid.split-qual-id-rev
          (rs2.string, lqual, id)
        Nil ->
          val (qual, id) = rid.split-qual-id-rev
          (qual, "", id)
        _ -> fail("Name split-id-name-rev: illegal locally qualified name: " ++ rs.string)
    fun split-name(s: string): <exn> (string, string, string)
      if s.ends-with(")").bool then // operator
        val (rop, rest) = s.list.reverse.span(fn(c) c != '(')
        match rest
          Cons('(', rs2) ->
            val (qual, lqual, id) = rs2.split-id-name-rev
            (qual, lqual, id ++ rop.string)
          _ -> fail("Name split-name: unmatched parenthesis in name: " ++ s)
      else s.list.split-id-name-rev
    val (q, lq, id) = s0.split-name
    new-locally-qualified(q,lq,id)

fun is-module-name(n: name): bool
  n.nameStem == ""

fun is-qualified(n: name): bool
  n.nameModule != ""

fun is-locally-qualified(n): bool
  n.nameLocalQual != ""

fun is-symbol-name(n: name): bool
  n.nameStem.is-symbol-id

fun is-constructor-name(n: name): bool
  match n.nameStem.slice.next
    Just((c, _)) | c.is-upper -> True
    Just(('@', r)) -> 
      match r.next
        Just((c, _)) | c.is-upper -> True
        _ -> False
    _ -> False

fun is-wildcard(n: name): bool
  match n.nameStem.slice.next
    Just(('_', _)) -> True
    Just(('@', r)) -> r.next.map(fn((c, _)) c == '_').default(False)
    _ -> False

fun is-hidden-name(n: name): bool
  n.nameStem.starts-with("@").bool

fun missing-qualifier(current-mod: name, n: name, qname: name): string
  val missing0 = qname.show-plain.list.reverse.drop(n.show-plain.count).reverse.string
  val standard = [current-mod.show, "std/core/types", "std/core/hnd", "std/core"]
  val missing = 
        match standard.filter(fn(std) (std ++ "/").is-prefix-of(missing0))
          Cons(std, _) -> missing0.list.drop(std.count).string
          _ -> missing0
  if missing.starts-with(implicit-namespace ++ "/").bool then "?" ++ missing.list.drop(implicit-namespace.count + 1).string
  else missing

val name/nil = "".new-name

fun is-nil(Name(m, _, _, _, n, _)): bool
  n == "" && m == ""

fun qualify(a: name, b: name): name
  match (a, b)
    (Name(m, hm, _, 0, _, 0), Name(_, 0, l, hl, n, hn)) -> Name(m, hm, l, hl, n, hn)
    (Name(m1, _, _, 0, _, 0), name as Name(m2)) | m1 == m2 -> name
    _ ->
      trace("Cannot use qualify on qualified names " ++ a.show-fully-explicit ++ ", " ++ b.show-fully-explicit)
      new-name("")

fun unqualify(Name(_, _,l, hl, n, hn)): name
  Name("", 0, l, hl, n, hn)

fun qualifier(Name(m, hm)): name
  Name(m, hm, "", 0, "", 0)

fun name-as-module-name(n: name): name
  new-module-name(join(n.nameModule, join(n.nameLocalQual, n.nameStem)))

fun qualify-locally(nl: name, n: name): <exn> name
  match nl
    Name(l, _, _, 0, _, 0) ->
      new-locally-qualified(n.nameModule, join(l, n.nameLocalQual), n.nameStem)
    _ -> fail("common/name/qualify-locally: illegal qualification: " ++ nl.show-explicit ++ ", " ++ n.show-explicit)

// Move the module qualifier to the local qualifier
fun requalify-locally(n: name): name
  if n.nameModule == "" then n else new-locally-qualified("", join(n.nameModule, n.nameLocalQual), n.nameStem)

// Only keep the stem
fun unqualify-full(n: name): name
  Name("", 0, "", 0, n.nameStem, n.hashStem)

// Full qualifier: module + local qualifier
fun full-qualifier(n: name): string
  n.unqualify-locally.nameModule

// Add the local qualifier to the module qualifier
fun unqualify-locally(n: name): name
  if n.nameLocalQual == "" then n else new-qualified(join(n.nameModule, n.nameLocalQual), n.nameStem)

fun unqualify-as-module-name(n: name): name
  new-module-name(join(n.nameModule, n.nameLocalQual))

// Module paths
fun split-module-name(n: name): list<string>
  n.nameModule.split("/")

fun unsplit-module-name(l: list<string>): name
  l.join("/").new-module-name

fun merge-common-path(n1: name, n2: name): name
  fun merge(l1: list<string>, l2: list<string>): list<string>
    match (l1, l2)
      (Cons(m, ms), Cons(n, ns)) -> 
        if m == n && ms.zipwith(ns, fn(i, j) -> i == j).all(fn(i) -> i) then
          Cons(m, ms) ++ ns.drop(ms.length)
        else
          Cons(m, merge(pretend-decreasing(ms), Cons(n, ns)))
      (Cons(m, ms), ns) -> Cons(m, merge(pretend-decreasing(ms), ns))
      (_, ns) -> ns
  val ns = n2.split-module-name
  val ms = n1.split-module-name
  val new = ms.merge(ns).unsplit-module-name
  new

fun split-local-qual-name(n: name): list<string>
  n.nameLocalQual.split("/")

fun to-constructor-name(n: name): name
  n.name-map-stem fn(stem)
    match stem.list
      Cons('@', Cons(c, cs)) -> Cons('@', Cons(c.to-upper, cs)).string // keep hidden names hidden
      Cons(c, cs) -> Cons(c.to-upper, cs).string
      _ -> stem

fun to-var-name(n: name): name 
  fun to-lowers(l: list<char>): list<char>
    match l
      Cons(c, cs) | c.is-upper -> Cons(c.to-lower, to-lowers(cs))
      _ -> l
  n.name-map-stem fn(stem)
    match stem.list
      Cons('@', cs) -> Cons('@', cs.to-lowers).string // keep hidden names hidden
      cs -> cs.to-lowers.string

fun to-handler-con-name(n: name): name
  make-hidden-name("Hnd", n)

fun name/starts-with(n: name, s: string): bool
  n.nameStem.starts-with(s).bool

fun prepend(s: string, n: name): name
  val sl = s.list
  val new = match n.nameStem.list
    Cons('@', t) -> match sl
      Cons('@', _) -> sl ++ t // Keep hidden names hidden
      _ -> Cons('@', sl ++ t)
    t -> sl ++ t
  new-qualified(n.nameModule, new.string)

fun postpend(n: name, post: string): name
  if n.is-symbol-name then // we must always end in symbols for operators so postpend inserts before the symbols
    n.name-map-stem fn(stem)
      val (rsyms, rid) = stem.list.reverse.span(fn(c) !c.is-id-char)
      val start = if rid.is-empty || rid.string == "@" then "@x" else rid.reverse.string // ensure it becomes a valid lowerid
      start ++ post ++ rsyms.reverse.string
  else n.name-map-stem fn(stem)
    val (xs, ys) = stem.list.reverse.span(fn(c) c == '?' || c == '\'')
    ys.reverse.string ++ post ++ xs.reverse.string

// Hidden names
fun make-hidden(n: name): name
  prepend("@", n)

fun make-hidden-name(s: string, n: name): name
  prepend("." ++ s ++ "-", n)

fun unmake-hidden(n: name, pre: string): <exn> name
  n.name-map-stem fn(stem)
    if stem.starts-with("@" ++ pre ++ "-").bool then
      stem.slice.drop(2 + pre.count).string
    else fail("common/name/unmake-hidden: expecting hidden name prefixed with @" 
              ++ pre ++ "-, but found: " ++ n.show)

fun new-hidden-name-ex(base: string, s: string): name
  make-hidden-name(base, s.new-name)

fun new-hidden-name(base: string): name
  make-hidden(base.new-name)

fun to-unique-name(i: int, n: name): name
  n.postpend("@" ++ i.show)

fun to-hidden-unique-name(i: int, pre: string, n: name): name
  make-hidden-name(pre, to-unique-name(i, n))

fun make-fresh-hidden-name(s: string, n: name, r: range)
  val idFromPos = fn(p) -> "-l" ++ p.line.show ++ "-c" ++ p.col.show
  make-hidden-name(s, n.postpend(r.start.idFromPos))

fun hidden/starts-with(n: name, pre: string): bool
  n.nameStem.starts-with("@" ++ pre).bool ||
    n.nameStem.starts-with("@" ++ pre ++ "-").bool

// Various special names

fun new-padding-name(i: int): name
  new-hidden-name-ex("padding", i.show)

fun is-padding-name(n: name): bool
  n.hidden/starts-with("padding")

fun new-cctx-name(s: string): name
  new-hidden-name-ex("cctx", s)

fun is-cctx-name(n: name): bool
  n.hidden/starts-with("cctx")

fun new-field-name(i: int): name
  new-hidden-name-ex("field", i.show)

fun is-field-name(n: name): bool
  n.hidden/starts-with("field")

fun new-implicit-typevar-name(i: int): name
  new-hidden-name-ex("tv", i.show)

fun is-implicit-typevar-name(n: name): bool
  n.hidden/starts-with("tv")

fun new-hidden-external-name(n: name): name
  make-hidden-name("extern", n)

fun is-hidden-external-name(n: name): bool
  n.hidden/starts-with("extern")

// Create a constructor creator name from the constructor name.
// Used if special creation functions are used for the constructor.
// in particular for the case of optional arguments.
fun new-creator-name(n: name): name
  make-hidden-name("create", n)

fun is-creator-name(n: name): bool
  n.hidden/starts-with("create")

fun is-early-bind-name(n: name): bool
  n.is-handle-name || n.is-creator-name

// Create a handler type name from an effect type name.
fun to-handler-name(n: name): name
  make-hidden-name("hnd", n)

fun is-handler-name(n: name): bool
  n.hidden/starts-with("hnd")

// Create an effect type name from an operations type name.
fun from-handler-name(n: name): <exn> name
  n.unmake-hidden("hnd")

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
  n.hidden/starts-with("ops")

// Create an effect type name from an operations type name.
fun from-operations-name(n: name): <exn> name
  n.unmake-hidden("ops")

fun to-op-selector-name(n: name): name
  make-hidden-name("select", n)

// Is this an operations name?
fun is-op-selector-name(n: name): bool
  n.hidden/starts-with("select")

//  Create an effect type name from an operations type name.
fun from-op-selector-name(n: name): <exn> name
  n.unmake-hidden("select")

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
  n.hidden/starts-with("tag")

// Create a name for a value operation
fun to-value-operation-name(n: name): name
  make-hidden-name("val", n)

// Is this an name of a value operation?
fun is-value-operation-name(n: name): bool
  n.hidden/starts-with("val")

// Create an operation name from a value operation name
fun from-value-operations-name(n: name): <exn> name
  n.unmake-hidden("val")

// Create an operation name from either a value operation name or regular operations name
fun to-basic-operations-name(n: name): <exn> name
  if n.is-value-operation-name then n.from-value-operations-name else n

// Implicits

val implicit-namespace = "@implicit"
val implicit-namespace-name = implicit-namespace.new-module-name

fun is-implicit-param-name(n: name): bool
  match n.split-local-qual-name
    Cons(m, _) -> m == implicit-namespace
    _ -> False

fun to-implicit-param-name(n: name): <exn> name
  qualify-locally(implicit-namespace-name, n)

fun from-implicit-param-name(n: name): <exn> name
  match n.split-local-qual-name
    Cons(m, ms) | m == implicit-namespace -> qualify-locally(ms.unsplit-module-name, n.unqualify-full)
    _ -> n

fun split-implicit-param-name(n: name): (name, name)
  (n, n.unqualify-full)

// name to file path
fun module-name-to-path(n: name): string
  n.show.ascii-encode(True)

fun path-to-module-name(p: string): name
  fun decode(sl: list<char>): list<char> // TODO: Performance / do proper decoding
    val s = sl.string
    match sl
      _ | s.starts-with("_dash_").bool -> Cons('-', decode(pretend-decreasing(sl.drop(6))))
      Cons('_', Cons('_', t)) -> Cons('_', decode(pretend-decreasing(t)))
      Cons('_', t) -> Cons('/', decode(pretend-decreasing(t)))
      Cons('@', t) -> Cons('@', decode(pretend-decreasing(t)))
      Cons('\\', t) -> Cons('/', decode(pretend-decreasing(t)))
      Cons(c, t) -> Cons(c, decode(pretend-decreasing(t)))
      Nil -> Nil
  p.list.map(fn(c) if c.is-path-sep then '/' else c).decode.drop-while(fn(c) -> c == '_' || c == '.' || c == '/').string.new-module-name

// Ascii encode a name
// - on module names '/' becomes '_'
// - on normal names '-' becomes '_'
fun ascii-encode(n: string, is-module: bool): string
  fun encode-char(pre: char, c: char, post: char): string
    match c
      _ | c.is-alpha-num -> c.string
      '/' | is-module -> "_"
      '-' | !is-module && post.is-alpha-num -> "_"
      '@' | post.is-digit || post == ' ' || pre == ' ' -> "_"

      '_' -> "__"
      '.' -> "_dot_"
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
      Cons(pre, Cons(c, Cons(post, rest))) -> Cons(encode-char(pre, c, post), encode-chars2(Cons(c, Cons(post, rest)).pretend-decreasing))
      Cons(pre, Cons(c, Nil)) -> Cons(encode-char(pre, c, ' '), Nil)
      Cons(pre, Nil) -> Cons(pre.string, Nil)
      Nil -> Nil
  fun encode-chars(s: string): string
    encode-chars2((" " ++ s).list).join
  if n.head-char.default(' ').is-alpha-num then
    return n.encode-chars
  match n
    ""      -> "_null_"
    "@<>"   -> "_total_"
    "@<|>"  -> "_extend_"
    "@()"   -> "_unit_"
    "@(,)"  -> "_tuple2_"
    "@(,,)" -> "_tuple3_"
    "@(,,,)"-> "_tuple4_"
    "()"    -> "_Unit_"
    "(,)"   -> "_Tuple2_"
    "(,,)"  -> "_Tuple3_"
    "(,,,)" -> "_Tuple4_"
    "[]"    -> "_index_"
    _ -> n.encode-chars
import std/text/regex

effect parse<e>
  fun tryText(s: string): either<perror<e>, ()>
  fun unmark(i: int): ()
  fun reset(i: int): ()
  fun tryPattern(p: regex): either<perror<e>, list<string>>
  fun trySkip(i: int): either<perror<e>, ()>
  fun tryTake(i: int): either<perror<e>, string>
  fun labels(): list<string>
  final ctl fail(e: perror<e>): a
  fun offset(): int
  fun mark(): int

alias parser<r,a,e::E> = () -> <parse<r>|e> a

fun atomic(p: parser<r,a,e>): <parse<r>|e> a
  val n = mark()
  match try(p)
    Left(e) ->
      reset(n)
      fail(e)
    Right(r) ->
      unmark(n)
      r

fun between(open: parser<r,a,e>, close: parser<r,a,e>, mid: parser<r,b,e>): <parse<r>|e> b
  productL({productR(open,mid)},close)

value type charQuery
  OneOf(text: string)
  Ranges(ranges: list<(char, char)>)

fun closeParen(): parse<e> ()
  text(")")
fun colon(): parse<e> ()
  text(":")
fun comma(): parse<e> ()
  text(",")
fun crlf(): parse<e> ()
  text("\r\n")
fun endOfString(): parse<e> ()
  with atomic
  val posMarker = offset()
  match tryTake(1)
    Left(_) -> ()
    Right(_) -> fail(Expected("End of string", Position(posMarker)))

type perror<e>
  Expected(expected: string, pos: position)
  ExpectedPatternMatch(pat: string, pos: position)
  NotEnough(i: int, pos: position)
  In(label: string, pos: position, err: perror<e>)
  UserDefined(err: e)
  ExpectedCharQuery(q: charQuery, pos: position)

fun failHere(e: (position -> perror<r>)): parse<r> a
  fail(e(Position(offset())))

fun halve(first: parser<r,f,e>, separator: parser<r,s,e>, second: parser<r,s,e>): <parse<r>|e> (f, s)
  val a = first()
  separator()
  val b = second()
  (a, b)

fun literal(t: string): <parse<r>|e> string
  text(t)
  t

fun many(p: parser<r,a,e>): <parse<r>|e> list<a>
  match optional(p)
    Just(a) -> 
      val x = many(p)
      Cons(a, x)
    Nothing -> []

fun many1(p: parser<r,a,<div|e>>): <parse<r>,div|e> list<a>
  val a = p()
  Cons(a, many(p))

fun newline(): <parse<r>|e> ()
  text("\n")

fun nonWhitespace(): <parse<r>|e> string
  takeWhile1(Ranges([('!', '~')]))

fun numeric(): <parse<r>|e> int
  with atomic
  val numQuery = Ranges([('0', '9')])
  val text = takeWhile1(numQuery)
  match parse-int(text)
    Just(i) -> i
    Nothing -> failHere(fn(p) ExpectedCharQuery(numQuery, p))

fun openParen(): <parse<r>|e> ()
  text("(")

fun optional(p: parser<r,a,e>): <parse<r>|e> maybe<a>
  or(fn() Just(p()), fn() Nothing)

fun or(p1: parser<r,a,e>, p2: parser<r,a,e>): <parse<r>|e> a
  val o1 = offset()
  match try(p1)
    Left(e) ->
      if offset() == o1 then 
        p2() 
      else 
        fail(e)
    Right(r) -> r

fun ors(ps: list<parser<r,a,<exn|e>>>): <parse<r>,exn|e> a
  match ps
    Nil -> fail(Expected("List size > 1 for or parser", Position(offset())))
    Cons(p1, Cons(p2, Nil)) -> or(p1, p2)
    Cons(p, pp) -> or(p, fn() ors(pp))

fun productL(a: parser<r,a,e>, b: parser<r,b,e>): <parse<r>|e> a
  match try(a)
    Left(e) -> fail(e)
    Right(r) ->
      b()
      r

fun productR(a: parser<r,a,e>, b: parser<r,b,e>): <parse<r>|e> b
  match try(a)
    Left(e) -> fail(e)
    Right(_) ->
      val vb = b()
      vb

fun reraise(p: parser<r,either<perror<r>,a>,e>): <parse<r>|e> a
  match p()
    Left(e) -> fail(e)
    Right(r) -> r

fun takeAdvance(s: sslice, i: int): (list<char>, sslice)
  if i == 0 || s.count == 0 then ([], s) else
    match s.next
      Nothing -> ([], s)
      Just((c,rest)) ->
        val (cs, newS) = takeAdvance(unsafe-decreasing(rest), i - 1)
        (Cons(c, cs), newS)

fun startsWith(s: sslice, cs: list<char>): (bool, sslice, int)
  match cs
    Nil -> (True, s, 0)
    Cons(c', cs') ->
      match s.next
        Just((c, rest)) | c' == c ->
          val (r, re, i) = startsWith(rest.unsafe-decreasing, cs'.tail.unsafe-decreasing)
          (r, re, i + 1)
        _ -> (False, s, 0)

fun run(parser: parser<r,a,<exn|e>>, s: string): <exn|e> either<perror<r>, a>
  var p := Position(0)
  var rem := s.slice
  var marks := []
  handle(parser)
    return(a) Right(a)
    fun tryTake(i: int)
      if i > rem.count then Left(NotEnough(i, p))
      else
        val (taken, rest) = rem.takeAdvance(i)
        rem := rest
        p := increment(p, i)
        Right(taken.string)
    fun trySkip(i: int)
      if i > rem.count then Left(NotEnough(i, p))
      else
        rem := rem.advance(i)
        p := increment(p, i)
        Right(())
    fun tryText(t: string)
      val (v, rem', cnt) = rem.startsWith(t.list)
      if v then
        rem := rem'
        p := increment(p, cnt)
        Right(())
      else Left(Expected(t, p))
    final ctl fail(e)
      Left(e)
    fun offset()
      p.offset
    fun tryPattern(pat: regex)
      match pat.exec(rem)
        Nil -> 
          Left(ExpectedPatternMatch(pat.source, p))
        ms ->
          val c = ms[0].default("".slice).count
          rem := rem.advance(c)
          p := increment(p, c)
          Right(ms.map(fn(s') s'.string))
    fun mark()
      marks := marks ++ [(rem, p)]
      marks.length
    fun unmark(i: int)
      marks := marks.take(i)
      ()
    fun reset(i: int)
      match marks[i]
        Nothing -> throw("Invalid Mark: " ++ i.show)
        Just((_, _)) ->
          marks := marks.take(i)
          ()
    fun labels()
      []

fun scope(t: string, p: parser<r,a,e>): <parse<r>|e> a
  val off = offset()
  match try({scope1(t, p)})
    Left(e) -> fail(In(t, Position(off), e))
    Right(r) -> r
      
fun scope1(t: string, p: parser<r,a,e>): <parse<r>|e> a
  with override
    final ctl fail(e) fail(e)
    fun offset() offset()
    fun labels() Cons(t, labels())
    fun mark() mark()
    fun unmark(i) unmark(i)
    fun reset(i) reset(i)
    fun tryTake(i) tryTake(i)
    fun trySkip(i) trySkip(i)
    fun tryText(s) tryText(s)
    fun tryPattern(pat) tryPattern(pat)
  p()

fun sep1(s: parser<r,s,<div|e>>, p: parser<r,a,<div|e>>): <parse<r>,div|e> list<a>
  Cons(p(),many
    s()
    p()
  )

fun skipUntil(q: charQuery): <parse<r>|e> ()
  val p = notInPattern(q)
  takePattern(p.regex)
  ()

fun notInPattern(q: charQuery): string
  match q
    OneOf(t) -> "^[^" ++ t ++ "]"
    Ranges(chars) ->
      chars.foldl("^") fn(acc:string, v)
        val (c1:char, c2:char) = v
        val p = "[^" ++ c1.show ++ "-" ++ c2.show ++ "]"
        if acc.is-empty then p else acc ++ "|" ++ p

fun skipWhile(q: charQuery): <parse<r>|e> ()
  takePattern(q.toPattern.regex)
  ()

fun toPattern(q: charQuery): string
  match q
    OneOf(t) -> "[" ++ t ++ "]"
    Ranges(chars) ->
      chars.foldl("^") fn(acc:string, v)
        val (c1:char, c2:char) = v
        val p = "[" ++ c1.show ++ "-" ++ c2.show ++ "]"
        if acc.is-empty then p else acc ++ "|" ++ p

fun skipWhitespace(): <parse<r>|e> ()
  skipWhile(OneOf(" \t\r"))

fun slash(): <parse<r>|e> ()
  text("/")

fun space(): <parse<r>|e> ()
  text(" ")

fun take(i: int): <parse<r>|e> string
  reraise({tryTake(i)})

val alnum = "^[a-zA-Z0-9]+".regex()
fun takeAlphanum(): <parse<r>|e> string
  takePattern(alnum)

val alnums = "^[a-zA-Z0-9]+".regex() 
fun takeAlphanum1(): <parse<r>|e> string
  takePattern(alnums)

fun takePattern(p: regex): <parse<r>|e> string
  val res = reraise({tryPattern(p)})
  res[0].default("")

fun takePatterns(p: regex): <parse<r>|e> list<string>
  reraise({tryPattern(p)})

fun takeUntil(q: charQuery): <parse<r>|e> string
  takePattern(notInPattern(q).regex)

fun takeWhile(q: charQuery): <parse<r>|e> string
  takePattern(q.toPattern.regex)

fun takeWhile1(q: charQuery): <parse<r>|e> string
  val initial = offset()
  val res = takePattern(q.toPattern.regex)
  if offset() == initial then fail(ExpectedCharQuery(q, Position(initial)))
  else res

fun takeWhitespace(): <parse<r>|e> string
  takeWhile(OneOf(" \t\r"))

fun text(t: string): <parse<r>|e> ()
  reraise({tryText(t)})

fun token(t: string): <parse<r>|e> string
  text(t)
  t

fun token(p: parser<r,a,e>): <parse<r>|e> a
  val res = p()
  skipWhitespace()
  res

fun tokenize(p: parser<r,a,e>): <parse<r>,div|e> list<string>
  sep1(skipWhitespace,nonWhitespace)

fun try(p: parser<r,a,e>): <parse<r>|e> either<perror<r>,a>
  with override
    return(a) Right(a)
    final ctl fail(e) Left(e)
    fun labels() labels()
    fun offset() offset()
    fun mark() mark()
    fun unmark(i) unmark(i)
    fun reset(i) reset(i)
    fun tryTake(i) tryTake(i)
    fun trySkip(i) trySkip(i)
    fun tryText(t) tryText(t)
    fun tryPattern(pat) tryPattern(pat)
  p()

struct position { offset: int }

fun increment(pos: position, i: int): position
  Position(pos.offset + i)

fun show(e: perror<e>, errShow: (e) -> string): string
  match e
    ExpectedCharQuery(q, p) -> "Expected " ++ q.show ++ " at " ++ p.show
    ExpectedPatternMatch(pat, p) -> "Expected pattern " ++ pat ++ " at " ++ p.show
    Expected(t, p) -> "Expected " ++ t ++ " at " ++ p.show
    NotEnough(i, p) -> "Not enough input at " ++ p.show ++ ", expected " ++ i.show
    In(label, p, err) -> "In " ++ label ++ " at " ++ p.show ++ ": " ++ show(err, errShow)
    UserDefined(err) -> errShow(err) 

fun show(q: charQuery): string
  match q
    OneOf(t) -> "one of " ++ t
    Ranges(chars) ->
      chars.foldl("") fn(acc:string, v)
        val (c1:char, c2:char) = v
        if acc.is-empty then c1.show ++ "-" ++ c2.show
        else acc ++ ", " ++ c1.show ++ "-" ++ c2.show

fun show(p: position): string
  p.offset.show
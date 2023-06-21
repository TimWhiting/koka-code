import std/text/regex
import std/num/float64

pub effect parse<e>
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

pub alias parser<r,a,e::E> = () -> <parse<r>|e> a

pub fun atomic(p: parser<r,a,e>): <parse<r>|e> a
  val n = mark()
  match tryParse(p)
    Left(e) ->
      reset(n)
      fail(e)
    Right(r) ->
      unmark(n)
      r

pub fun between(open: parser<r,a,e>, close: parser<r,a,e>, mid: parser<r,b,e>): <parse<r>|e> b
  productL({productR(open,mid)},close)

pub value type charQuery
  OneOf(text: string)
  Ranges(ranges: list<(char, char)>)

pub type perror<e>
  Expected(expected: string, pos: position)
  ExpectedPatternMatch(pat: string, pos: position)
  NotEnough(i: int, pos: position)
  In(label: string, pos: position, err: perror<e>)
  UserDefined(err: e)
  ExpectedCharQuery(q: charQuery, pos: position)

pub fun failHere(e: (position -> perror<r>)): parse<r> a
  fail(e(Position(offset())))

pub fun halve(first: parser<r,f,e>, separator: parser<r,s,e>, second: parser<r,s,e>): <parse<r>|e> (f, s)
  val a = first()
  separator()
  val b = second()
  (a, b)

pub fun literal(t: string): <parse<r>|e> string
  text(t)
  t

pub fun many(p: parser<r,a,e>): <parse<r>|e> list<a>
  match optional(p)
    Just(a) -> 
      val x = many(p)
      Cons(a, x)
    Nothing -> []

pub fun many1(p: parser<r,a,<div|e>>): <parse<r>,div|e> list<a>
  val a = p()
  Cons(a, many(p))

pub fun optional(p: parser<r,a,e>): <parse<r>|e> maybe<a>
  or(fn() Just(p()), fn() Nothing)

pub fun or(p1: parser<r,a,e>, p2: parser<r,a,e>): <parse<r>|e> a
  val o1 = offset()
  match tryParse(p1)
    Left(e) ->
      if offset() == o1 then 
        p2() 
      else 
        fail(e)
    Right(r) -> r

pub fun ors(ps: list<parser<r,a,<exn|e>>>): <parse<r>,exn|e> a
  match ps
    Nil -> fail(Expected("List size > 1 for or parser", Position(offset())))
    Cons(p1, Cons(p2, Nil)) -> or(p1, p2)
    Cons(p, pp) -> or(p, fn() ors(pp))

pub fun productL(a: parser<r,a,e>, b: parser<r,b,e>): <parse<r>|e> a
  match tryParse(a)
    Left(e) -> fail(e)
    Right(r) ->
      b()
      r

pub fun productR(a: parser<r,a,e>, b: parser<r,b,e>): <parse<r>|e> b
  match tryParse(a)
    Left(e) -> fail(e)
    Right(_) ->
      val vb = b()
      vb

pub fun reraise(p: parser<r,either<perror<r>,a>,e>): <parse<r>|e> a
  match p()
    Left(e) -> fail(e)
    Right(r) -> r

pub fun takeAdvance(s: sslice, i: int): (list<char>, sslice)
  if i == 0 || s.count == 0 then ([], s) else
    match s.next
      Nothing -> ([], s)
      Just((c,rest)) ->
        val (cs, newS) = takeAdvance(unsafe-decreasing(rest), i - 1)
        (Cons(c, cs), newS)

pub fun startsWith(s: sslice, cs: list<char>): (bool, sslice, int)
  match cs
    Nil -> (True, s, 0)
    Cons(c', cs') ->
      match s.next
        Just((c, rest)) | c' == c ->
          val (r, re, i) = startsWith(rest.unsafe-decreasing, cs'.tail.unsafe-decreasing)
          (r, re, i + 1)
        _ -> 
          (False, s, 0)


fun increment(pos: position, i: int): position
  Position(pos.offset + i)

pub fun run(parser: parser<r,a,<exn|e>>, s: string): <exn|e> either<perror<r>, a>
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
        p := p.increment(i)
        Right(taken.string)
    fun trySkip(i: int)
      if i > rem.count then Left(NotEnough(i, p))
      else
        rem := rem.advance(i)
        p := p.increment(i)
        Right(())
    fun tryText(t: string)
      val (v, rem', cnt) = rem.startsWith(t.list)
      if v then
        rem := rem'
        p := p.increment(cnt)
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
          // TODO: Assert that start of capture equals start of slice
          val c = ms[0].default("".slice).count
          rem := rem.advance(c)
          p := p.increment(c)
          Right(ms.map(fn(s') s'.string))
    fun mark()
      marks := marks ++ [(rem, p)]
      marks.length - 1
    fun unmark(i: int)
      marks := marks.take(i)
      ()
    fun reset(i: int)
      match marks[i]
        Nothing -> throw("Invalid Mark: " ++ i.show)
        Just((rem', p')) ->
          marks := marks.take(i)
          rem := rem'
          p := p'
          ()
    fun labels()
      []

pub fun scope(t: string, p: parser<r,a,e>): <parse<r>|e> a
  val off = offset()
  match tryParse({scope1(t, p)})
    Left(e) -> fail(In(t, Position(off), e))
    Right(r) -> r
      
pub fun scope1(t: string, p: parser<r,a,e>): <parse<r>|e> a
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

pub fun sep1(s: parser<r,s,<div|e>>, p: parser<r,a,<div|e>>): <parse<r>,div|e> list<a>
  Cons(p(),many
    s()
    p()
  )

pub fun skipUntil(q: charQuery): <parse<r>|e> ()
  val p = notInPattern(q)
  takePattern(p.regex)
  ()

pub fun notInPattern(q: charQuery): string
  match q
    OneOf(t) -> "^[^" ++ t ++ "]"
    Ranges(chars) ->
      chars.foldl("^") fn(acc:string, v)
        val (c1:char, c2:char) = v
        val p = "[^" ++ c1.show ++ "-" ++ c2.show ++ "]"
        if acc.is-empty then p else acc ++ "|" ++ p

pub fun skipWhile(q: charQuery): <parse<r>|e> ()
  //TODO: Encourage caching regexes for charQueries, or intern them?
  takePattern(q.toPattern.regex)
  ()

pub fun toPattern(q: charQuery): string
  match q
    OneOf(t) -> "[" ++ t ++ "]"
    Ranges(chars) ->
      chars.foldl("^") fn(acc:string, v)
        val (c1:char, c2:char) = v
        val p = "[" ++ c1.show ++ "-" ++ c2.show ++ "]"
        if acc.is-empty then p else acc ++ "|" ++ p

pub fun take(i: int): <parse<r>|e> string
  reraise({tryTake(i)})

pub fun takePattern(p: regex): <parse<r>|e> string
  val res = reraise({tryPattern(p)})
  res[0].default("")

pub fun takePatterns(p: regex): <parse<r>|e> list<string>
  reraise({tryPattern(p)})

pub fun takeUntil(q: charQuery): <parse<r>|e> string
  takePattern(notInPattern(q).regex)

pub fun takeWhile(q: charQuery): <parse<r>|e> string
  takePattern(q.toPattern.regex)

pub fun takeWhile1(q: charQuery): <parse<r>|e> string
  val initial = offset()
  val res = takePattern(q.toPattern.regex)
  if offset() == initial then fail(ExpectedCharQuery(q, Position(initial)))
  else res

pub fun takeWhitespace(): <parse<r>|e> string
  takeWhile(OneOf(" \t\r"))

pub fun text(t: string): <parse<r>|e> ()
  reraise({tryText(t)})

pub fun token(t: string): <parse<r>|e> string
  text(t)
  t

pub fun token(p: parser<r,a,e>): <parse<r>|e> a
  val res = p()
  skipWhitespace()
  res

pub fun tokenize(p: parser<r,a,e>): <parse<r>,div|e> list<string>
  sep1(skipWhitespace,nonWhitespace)

pub fun tryParse(p: parser<r,a,e>): <parse<r>|e> either<perror<r>,a>
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

pub value struct position { offset: int }

pub fun show(e: perror<e>, errShow: (e) -> string, input: string): string
  match e
    ExpectedCharQuery(q, p) -> "Expected " ++ q.show ++ " at " ++ p.show
    ExpectedPatternMatch(pat, p) -> "Expected pattern " ++ pat ++ " at " ++ p.show
    Expected(t, p) -> "Expected " ++ t ++ " at " ++ p.show ++ " but found " ++ showLineOffset(input, p.offset)
    NotEnough(i, p) -> "Not enough input at " ++ p.show ++ ", expected " ++ i.show
    In(label, p, err) -> "In " ++ label ++ " at " ++ p.show ++ ": " ++ show(err, errShow, input)
    UserDefined(err) -> errShow(err) 

fun showLineOffset(s: string, offset: int): string
  val sub = s.slice.advance(offset)
  sub.advance(-10).substr(0, min(offset, 10)).string ++ "(" ++ sub.substr(0,1).string ++ ")" ++ sub.substr(1, 10).string

pub fun show(q: charQuery): string
  match q
    OneOf(t) -> "one of " ++ t
    Ranges(chars) ->
      chars.foldl("") fn(acc:string, v)
        val (c1:char, c2:char) = v
        if acc.is-empty then c1.show ++ "-" ++ c2.show
        else acc ++ ", " ++ c1.show ++ "-" ++ c2.show

pub fun show(p: position): string
  p.offset.show

// Common
val leadingDotRegex = r"^[+-]?\.[0-9]+([eE][+-]?[0-9]+)?".regex() 
val wholeFloatRegex = r"^[+-]?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?".regex() 

pub fun parseFloat(): <parse<r>|e> float64
  val result = parseWholeFloat.or(parseLeadingDotFloat)
  val pos = Position(offset())
  match parse-float64(result)
    Just(i) -> i
    Nothing -> failHere(fn(p) Expected("float", pos))

fun parseWholeFloat(): <parse<r>|e> string
  takePattern(wholeFloatRegex)

fun parseLeadingDotFloat(): <parse<r>|e> string
  takePattern(leadingDotRegex)

val wholeNumRegex = r"^[0-9]+".regex() 
fun parseInt(): <parse<r>|e> int
  match tryParse({takePattern(wholeNumRegex)})
    Left(e) -> fail(e)
    Right(x) -> 
      val pos = Position(offset())
      match parse-int(x)
        Just(i) -> i
        Nothing -> failHere(fn(p) Expected("int", pos))


val alphaRegex = "^[a-zA-Z]".regex()
pub fun takeAlpha(): <parse<r>|e> string
  takePattern(alphaRegex)

val alnumRegex = "^[a-zA-Z0-9]+".regex()
pub fun takeAlphanum(): <parse<r>|e> string
  takePattern(alnumRegex)

pub fun takeAlphanum1(): <parse<r>|e> string
  takePattern(alnumRegex)

pub fun skipWhitespace(): <parse<r>|e> ()
  skipWhile(OneOf(" \t\r\n"))

pub fun parseSlash(): <parse<r>|e> ()
  text("/")

pub fun parseSpace(): <parse<r>|e> ()
  text(" ")

pub fun nonWhitespace(): <parse<r>|e> string
  takeWhile1(Ranges([('!', '~')]))

pub fun parseOpenParen(): <parse<r>|e> ()
  text("(")

pub fun parseCloseParen(): parse<e> ()
  text(")")

pub fun parseColon(): parse<e> ()
  text(":")

pub fun parseComma(): parse<e> ()
  text(",")

pub fun parseCrlf(): parse<e> ()
  text("\r\n")

pub fun parseNewline(): <parse<r>|e> ()
  text("\n")

pub fun parseEndOfLine(): parse<e> ()
  parseNewline.or(parseCrlf)

pub fun parseEndOfInput(): parse<e> ()
  with atomic
  val posMarker = offset()
  match tryTake(1)
    Left(_) -> ()
    Right(_) -> fail(Expected("End of string", Position(posMarker)))

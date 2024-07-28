import compiler/common/range
import compiler/syntax/lexeme
import compiler/common/name
import std/data/word-set

pub struct state
  pos: pos
  startPos: pos
  states: list<int>
  retained: list<sslice>
  previous: char
  current: sslice
  previousLex: lex
  rawEnd: string;

pub alias action = sslice -> pure (state -> pure (state -> pure (maybe<lex>, state)));

fun pos/before(p: pos)
  p(col=max(1, p.col - 1))

fun strip-parens(s: sslice)
  match s.string.list.reverse
    Cons(')', cs) -> 
      match cs.span(fn(c) { c != '(' })
        (op, Cons('(', qual)) -> (op ++ qual).reverse.string
        _ -> s.string
    _ -> s.string

fun head(s: list<a>): exn a
  match s
    Cons(x, _) -> x
    Nil -> throw("head")

fun token(lex: (sslice -> pure lex)): action
  fn(bs: sslice) fn(st0: state) fn(st1: state) (Just(lex(bs)), st1)

fun lex/string(lex: (string -> pure lex)): action
  token(fn(bs: sslice) lex(bs.string))

fun lex/next(state: int, action: action): action
  fn(bs: sslice) fn(st0: state) fn(st1: state)
     val (x, State(p, sp, sts, ret, prev, cur, pL, rE)) = action(bs)(st0)(st1)
     (x, State(p, sp, Cons(state, sts), ret, prev, cur, pL, rE))

fun push(action: action): action
  fn(bs: sslice) fn(st0: state) fn(st1: state)
     next(st1.states.list/head.unjust, action)(bs)(st0)(st1)

fun pop(action: int -> action): action
  fn(bs: sslice) fn(st0: state) fn(st1: state)
    val sts = st1.states.tail
    val sts' = if sts.is-nil then [0] else sts
    val (x, State(p, sp, _, ret, prev, cur, pL, rE)) = action(sts'.head)(bs)(st0)(st1)
    (x, State(p, sp, sts', ret, prev, cur, pL, rE))

fun more(f: (sslice -> pure sslice)): action
  fn(bs: sslice) fn(st0: state) fn(State(p, sp, sts, ret, prev, cur, pL, rE): state) 
    (Nothing, State(p, sp, sts, Cons(f(bs), ret), prev, cur, pL, rE))

fun less(n: int, action: action)
  fn(bs: sslice) fn(st0: state) fn(State(_, sp, sts, ret, prev, _, pL, rE): state)
    val bs2 = st0.current.take(n)
    val pos2 = st0.pos.pos-moves8(bs2)
    val st2 = State(pos2, sp, sts, ret, prev, st0.current.drop(n), pL, rE)
    action(bs2)(st0)(st2)

fun withmore(action: action)
  fn(bs: sslice) fn(st0: state) fn(State(p, sp, sts, ret, prev, cur, pL, rE): state)
    action(Cons(bs, ret).reverse.map(string).join("").slice)(st0)(State(p, sp, sts, [], prev, cur, pL, rE))

fun raw-delim(f: action): action
  fn(bs: sslice) fn(st0: state) fn(st1: state)
    val s = bs.string
    val delim = "\"" ++ "#".repeat(s.count - 1)
    f(bs)(st0)(st1(rawEnd=delim))

fun with-raw-delim(f: (string, string) -> pure action): action
  fn(bs: sslice) fn(st0: state) fn(st1: state)
    f(bs.string, st1.rawEnd)(bs)(st0)(st1)

alias alexInput = state

fun unsafe-char(kind: string, s: string)
  LexError("unsafe character in " ++ kind ++ ": " ++ s.head) // TODO: Fix this

// Reserved
val special-names = [ "{", "}"
    , "(", ")"
    , "<", ">"
    , "[", "]"
    , ";", ","
]

val reserved-names = ["infix", "infixr", "infixl", "prefix", "postfix"
              , "type", "alias"
              , "struct", "enum", "con"
              , "val", "fun", "fn", "extern", "var"
              , "ctl", "final", "raw"
              , "if", "then", "else", "elif"
              , "return", "match", "with", "in"
              , "forall", "exists", "some"
              , "pub", "abstract"
              , "module", "import", "as"

              // effect handlers
              , "handler", "handle"
              , "effect", "receffect"
              , "named"
              , "mask"
              , "override"   

              // deprecated
              , "private", "public"  // use pub
              , "rawctl", "brk"      // use raw ctl, and final ctl

              // alternative names for backwards paper compatability
              , "control", "rcontrol", "except"
              , "ambient", "context" // use effcet
              , "inject"       // use mask
              , "use", "using" // use with instead
              , "function"     // use fun
              , "instance"     // use named

              // future reserved
              , "interface"
              , "unsafe"

              // operators
              , "="
              , "."
              , ":"
              , "->"
              , "<-"
              , ":="
              , "|"]

fun is-reserved(name: string)
  reserved-names.any(fn(n) n == name)

// val reserved-names = 
//       delay({
//         string-pool().add-all(
//         ["infix", "infixr", "infixl", "prefix", "postfix"
//               , "type", "alias"
//               , "struct", "enum", "con"
//               , "val", "fun", "fn", "extern", "var"
//               , "ctl", "final", "raw"
//               , "if", "then", "else", "elif"
//               , "return", "match", "with", "in"
//               , "forall", "exists", "some"
//               , "pub", "abstract"
//               , "module", "import", "as"

//               // effect handlers
//               , "handler", "handle"
//               , "effect", "receffect"
//               , "named"
//               , "mask"
//               , "override"   

//               // deprecated
//               , "private", "public"  // use pub
//               , "rawctl", "brk"      // use raw ctl, and final ctl

//               // alternative names for backwards paper compatability
//               , "control", "rcontrol", "except"
//               , "ambient", "context" // use effcet
//               , "inject"       // use mask
//               , "use", "using" // use with instead
//               , "function"     // use fun
//               , "instance"     // use named

//               // future reserved
//               , "interface"
//               , "unsafe"

//               // operators
//               , "="
//               , "."
//               , ":"
//               , "->"
//               , "<-"
//               , ":="
//               , "|"])
//     })

// fun is-reserved(name: string)
//   reserved-names.force.is-interned(name)

fun is-prefix-op(name: string)
  name == "!" || name == "~"

fun string/is-malformed(name: string)
  name.list.charlist/is-malformed

fun charlist/is-malformed(name: list<char>)
  match name
    Cons('-', Cons(c, cs)) -> !c.is-alpha || cs.is-malformed
    Cons(c, Cons('-', cs)) -> !c.is-alpha || c.is-digit || cs.is-malformed
    Cons(_, cs) -> cs.is-malformed
    Nil -> False

val message-malformed
  = "malformed identifier: a dash must be preceded by a letter or digit, and followed by a letter"

fun newQName(s': string)
  val s = s'.list 
  val (rname, rsmod) = s.reverse.span(fn(c) { c != '/' })
  match rsmod // TODO: First case needs condition on rname == Nil
    Cons('/', Cons('/', rmod)) -> new-qualified(rmod.reverse.string, "/")
    Cons('/', rmod) -> new-qualified(rmod.reverse.string, rname.reverse.string)
    _ -> s.string.new-name

fun char/from-char-esc(c)
  match c
    'n' -> '\n'
    'r' -> '\r'
    't' -> '\t'
    _ -> c

fun sslice/from-char-esc(s: sslice)
  s.drop(2).truncate().extend(1)

fun char/from-hex-esc(s: sslice)
  '\n' // TODO: Implement from-hex-esc

fun sslice/from-hex-esc(s: sslice)
  s.drop(3).extend(-1)
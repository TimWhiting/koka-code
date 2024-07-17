import newstd/text/parse
import std/text/regex
import std/text/unicode
import std/os/path
import std/os/file
import std/num/float64
import compiler/common/name
import compiler/common/range
import compiler/syntax/lexeme

inline fun forward-slash()
  token("/")

inline fun open-paren()
  token("(")

inline fun close-paren()
  token(")")

inline fun underscore()
  token("_")

inline fun dash()
  token("-")

val spacesRegex = "^[ ]+".regex()
inline fun space()
  takePattern(spacesRegex).string

inline fun tab()
  token("\t")

val graphicRegex = "^[\x21-\x7E]".regex()
inline fun graphic()
  takePattern(graphicRegex).string

val symbolRegex = r"^[\$%&*+~!/\\^~=.:\-?<>|]".regex()
inline fun symbol()
  takePattern(symbolRegex).string

val specialRegex = "^[()[\\]{};,]".regex()
inline fun special()
  takePattern(specialRegex).string

val anglebarRegex = "^[<>]".regex()
inline fun anglebar()
  takePattern(anglebarRegex).string

val charExcRegex = r#"^[nrt\\\'\"]"#.regex();
inline fun char-esc()
  takePattern(charExcRegex).string

// Regular expressions

val newlineRegex = "^\r?\n".regex()
fun newline()
  takePattern(newlineRegex).string

// More utf8
val utf8Regex = "^([\xC2-\xDF][\x80-\xBF]|\xE0[\xA0-\xBF][\x80-\xBF]|[\xE1-\xEC][\x80-\xBF][\x80-\xBF])".regex();
fun utf8()
  takePattern(utf8Regex).string

fun linechar()
  [graphic, space, tab, utf8].ors

val graphicComment = "^[\x21-\x29\x2B-\x2E\x30-\x7E]".regex()
inline fun graphic-comment()
  takePattern(graphicComment).string

fun commentchar()
  [graphic-comment, space, tab, newline, utf8].ors

val hexDigitRegex2 = "^x[0-9a-fA-F]{2}".regex()
val hexDigitRegex4 = "^u[0-9a-fA-F]{4}".regex()
val hexDigitRegex6 = "^U[0-9a-fA-F]{6}".regex()
fun hexesc1()
  takePattern(hexDigitRegex2)

fun hexesc2()
  takePattern(hexDigitRegex4)

fun hexesc3()
  takePattern(hexDigitRegex6)

fun hex-esc()
  [hexesc1, hexesc2, hexesc3].ors.string

fun escape()
  token("\\") ++ [hex-esc, char-esc].ors

inline fun graphic-string()
  takePattern(graphicCharStringRegex).string

fun stringchar()
  [graphic-string, space, utf8].ors

val graphicCharRegex = r#"^[\x21-\x7E]"#.regex()
                             // skip "      skip \      also space
val graphicCharStringRegex = r#"^[\x21\x23-\x5B\x5D-\x7E ]"#.regex()
                             // skip '     skip \      also space
val graphicCharCharRegex = r#"^[\x21-\x26\x28-\x5B\x5D-\x7E ]"#.regex()

inline fun graphic-char()
  takePattern(graphicCharRegex)

inline fun charchar()
  [{takePattern(graphicCharCharRegex).string}, space, utf8].ors

val graphicStringRawRegex = "^[^\"]".regex()
fun graphic-stringraw()
  takePattern(graphicStringRawRegex).string

fun stringraw()
  [graphic-stringraw, space, tab, newline, utf8].ors

val idCharsRegex = "^[a-zA-Z0-9-_]+".regex()

val wildCardRegex = "^_[a-zA-Z0-9-_]*".regex()

val lowerIdRegex = "^[a-z][a-zA-Z0-9-_]*'*".regex()
fun lowerid()
  takePattern(lowerIdRegex)

val upperIdRegex = "^[A-Z][a-zA-Z0-9-_]*'*".regex()
fun upperid()
  takePattern(upperIdRegex)

fun conid()
  upperid()

val modulePathRegex = "^([a-z][a-zA-Z0-9-_]*!*/)+".regex()
fun modulepath()
  takePattern(modulePathRegex)

fun qvarid()
  modulepath().string ++ lowerid().string

fun qconid()
  modulepath().string ++ upperid().string

fun psymbols()
  [{many1(symbol).join}, forward-slash].ors

fun qidop()
  modulepath().string ++ open-paren() ++ psymbols() ++ close-paren()

fun idop()
  open-paren() ++ psymbols() ++ close-paren()

val hexLeadRegex = r"^0[xX]".regex();
fun hexadecimal()
  takePattern(leadingRegex).string ++ takePattern(hexLeadRegex).string ++ takePattern(integerRegex).string

val leadingHexDotRegex = r"^\.[0-9a-fA-F_]+([eEpP][+-]?[0-9a-fA-F_]+)?".regex() 
val wholeHexFloatRegex = r"^[0-9a-fA-F_]+((\.[0-9a-fA-F_]+)|([eEpP][+-]?[0-9a-fA-F_]+)|(\.[0-9a-fA-F_]+[eEpP][+-]?[0-9a-fA-F_]+)".regex() 
val integerRegex = r"^[0-9a-fA-F_]+".regex() 
fun integer()
  takePattern(leadingRegex).string ++ takePattern(integerRegex).string

val leadingRegex = r"^[+-]?".regex()
fun exp()
  takePattern(leadingRegex).string ++ integer()
  
fun decfloat()
  takePattern(leadingRegex).string ++ (fn() takePattern(wholeHexFloatRegex).string).or({takePattern(leadingHexDotRegex).string})

fun hexfloat()
  takePattern(leadingRegex).string ++ hexadecimal() ++ (fn() takePattern(wholeHexFloatRegex).string).or({takePattern(leadingHexDotRegex).string})

// Start on tokenizing
fun lex-space()
  with atomic
  LexWhite(space())

fun lex-newline()
  with atomic
  LexWhite(newline())

fun lex-start-comment()
  with atomic
  text("/*")
  val x = many(symbol)
  LexError("TODO")

fun lex-start-line-comment()
  with atomic
  text("//")
  val x = many(symbol)
  LexError("TODO")

fun lex-linedirective()
  with atomic
  newline()
  text("#")
  val x = many(symbol)
  LexError("TODO")

fun lex-qconid()
  with atomic
  LexCons(qconid().list.newQName)

fun lex-qvarid()
  with atomic
  LexId(qvarid().list.newQName)

fun lex-qidop()
  with atomic
  LexOp(qidop().list.stripParens.newQName)

fun lex-lowerid()
  with atomic
  val l = lowerid().string
  if l.isReserved then
    LexKeyword(l, "")
  else if l.list.isMalformed then
    LexError(messageMalformed)
  else
    LexId(l.new-name)

fun lex-conid()
  LexCons(conid().string.new-name)

fun lex-wildcard()
  LexWildCard(takePattern(wildCardRegex).string.new-name)

fun lex-special()
  LexSpecial(special())

fun lex-decfloat()
  with atomic
  val d = decfloat().split("_").join
  LexFloat(d.parse-float64.default(-1.0), d)

fun lex-hexfloat()
  with atomic
  val d = hexfloat().split("_").join
  LexFloat(d.parse-float64.default(-1.0), d)

fun lex-integer()
  with atomic
  val d = integer().split("_").join
  LexInt(d.parse-int.default(-1), d)

fun lex-or()
  LexOp(token("||").new-name)

fun lex-anglebar()
  with atomic
  var x := anglebar()
  val i = mark() 
  many1(anglebar).join
  reset(i)
  match x
    "|" -> LexKeyword(x, "")
    _ -> LexOp(x.new-name)

fun lex-idop()
  with atomic
  LexIdOp(idop().list.stripParens.string.new-name)

fun lex-symbols()
  with atomic
  val s = psymbols()
  if s.isReserved then
    LexKeyword(s, "")
  else if s.isPrefixOp then
    LexPrefix(s.new-name)
  else
    LexOp(s.new-name)

fun lex-stringbegin()
  with atomic
  text("\"")
  val inner = many({[stringchar, {token("\\") ++ char-esc()}, {token("\\") ++ hex-esc()}, newline].ors}).join
  val err = illegal-str.many()
  text("\"")
  match err
    Cons(e, _) -> e
    Nil -> LexString(inner) // TODO: Consider ending with an error

fun illegal-str() // TODO: This needs to be fixed
  with atomic
  val res = many1(graphic-stringraw).join
  LexError(res)

fun lex-rstringbegin()
  with atomic
  token("r") ++ many({token("#")}).join ++ token("\"")
  val inner = many({[stringraw].ors}).join
  val err = illegal-str.many
  token("\"") ++ many({token("#")}).join
  match err
    Cons(e, _) -> e
    Nil -> LexString(inner)

val notNewlineRegex = "^[^\\n]+".regex()
fun lex-linecomment()
  with atomic
  val start = token("//") ++ takePattern(notNewlineRegex).string
  LexComment(start ++ newline())

fun lex-charesc()
  with atomic
  text("\'\\")
  val c = char-esc()
  text("'")
  LexChar(c.head-char.unjust)

fun lex-hexesc()
  with atomic
  text("'\\")
  val c = hex-esc()
  text("'")
  LexChar(c.list.drop(3).head('*').fromCharEsc.string.head-char.unjust)

fun lex-char()
  with atomic
  text("'")
  val c = charchar()
  text("'")
  LexChar(c.head-char.unjust)

fun lex-emptychar()
  with atomic
  text("\'")
  val c = takeChars(1)
  text("\'")
  LexError("Illegal character literal: " ++ c)
  
fun lex-tab()
  with atomic
  val t = many1(tab)
  LexError("Illegal tab character: configure your editor to use spaces instead")

fun lex-unknown()
  with atomic
  val c = takeChars(1)
  LexError("Illegal character: " ++ c)

fun lex-default()
  with atomic
  [lex-space,lex-newline,lex-linecomment,lex-qconid,lex-qvarid,lex-qidop,lex-lowerid,lex-conid,lex-wildcard,lex-special,lex-charesc,lex-hexesc,lex-char,lex-decfloat,lex-hexfloat,lex-integer,lex-or,lex-anglebar,lex-idop,lex-symbols,lex-stringbegin,lex-rstringbegin].ors

fun stripParens(s: list<char>)
  match s.reverse
    Cons(')', cs) -> 
      match cs.span(fn(c) { c != '(' })
        (op, Cons('(', qual)) -> (op ++ qual).reverse
        _ -> s
    _ -> s

fun newQName(s: list<char>) 
  val (rname, rsmod) = s.reverse.span(fn(c) { c != '/' })
  match rsmod // TODO: First case needs condition on rname == Nil
    Cons('/', Cons('/', rmod)) -> new-qualified(rmod.reverse.string, "/")
    Cons('/', rmod) -> new-qualified(rmod.reverse.string, rname.reverse.string)
    _ -> s.string.new-name

fun fromCharEsc(c)
  match c
    'n' -> '\n'
    'r' -> '\r'
    't' -> '\t'
    _ -> c

fun unsafeChar(k: string, s: string): lex
  LexError("Unsafe character in " ++ k ++ ": " ++ s) //TODO: ++ showHex(4, s.list.head))

// Reserved
val specialNames = [ "{", "}"
    , "(", ")"
    , "<", ">"
    , "[", "]"
    , ";", ","
]

val reservedNames =  ["infix", "infixr", "infixl", "prefix", "postfix"
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

fun isReserved(name: string)
  reservedNames.any(fn(n) -> n == name) // TODO: Set

fun isPrefixOp(name: string)
  name == "!" || name == "~"

fun isMalformed(name: list<char>)
  match name
    Cons('-', Cons(c, cs)) -> !c.is-alpha || cs.isMalformed
    Cons(c, Cons('-', cs)) -> !c.is-alpha || c.is-digit || cs.isMalformed
    Cons(_, cs) -> cs.isMalformed
    Nil -> False

val messageMalformed
  = "malformed identifier: a dash must be preceded by a letter or digit, and followed by a letter"

type lex-part
  Default
  StringLit
  StringRaw
  Comment
  LineComment
  LineDirective

fun lexer(sourceName: string, lineNo: int, input: string)
  lexing(Source(sourceName, input), lineNo, input)

fun lex(source: source, lineNo: int, input: string): <console,div,exn> list<lexeme>
  match lexing(source, lineNo, input)
    Right(u) -> u
    _ -> Cons(Lexeme(range/null, LexError("Unexpected end of input")), Nil)

fun lexing(source: source, lineNo: int, input: string)
  // with parse(input.slice)
  run(input)
    var pos := Pos(source, 0, lineNo, 1)
    var result := Nil
    var cont := True
    var mode := Default
    while { cont }
      match tryParse(parseEndOfInput)
        Left ->
          val start = pos
          val startOff = offset()
          match tryParse(lex-default)
            Right(e) -> 
              // trace(e.show)
              val finalOffset = offset()
              val nlines = match e
                LexWhite(w) -> w.count("\n")
                LexComment(w) -> w.count("\n")
                _ -> 0
              val ncols = match e
                LexWhite(w) | w.contains("\n") -> w.list.reverse.take-while(fn(c) c != '\n').length  + 1
                LexComment(w) | w.contains("\n") -> w.list.reverse.take-while(fn(c) c != '\n').length + 1
                _ -> (finalOffset - startOff) + pos.col
              pos := Pos(source, finalOffset, start.line + nlines, col=ncols)
              result := Cons(Lexeme(Range(start, pos), e), result)
            Left(e) ->
              cont := False
              throw("Lexing error: \n\n" ++ e.perr/show(input, indent="  ", ?show=fn(s:string) s))
        Right ->
          cont := False
    result.reverse


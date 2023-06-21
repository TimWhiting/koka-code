import newstd/text/parse
import std/text/regex
import std/num/float64

struct token
  value: sexpr
  start: int
  end: int

type sexpr
  SBool(b: bool)
  SChar(c: string)
  SSymbol(s: string)
  SNumber(n: float64)
  SList(l: list<token>, r: maybe<token>)

fun show(t: token): div string
  show(t.value)

fun show(s: sexpr): div string
  match s
    SBool(b) -> if b then "#t" else "#f"
    SChar(c) -> r"#\" ++ c
    SSymbol(s1) -> s1
    SNumber(n) -> n.show()
    SList(l, Nothing) -> "(" ++ l.map(show).join(" ") ++ ")"
    SList(l, Just(r)) -> "(" ++ l.map(show).join(" ") ++ " . " ++ show(r) ++ ")"

val identifierRegex = r"^[a-zA-Z][a-zA-Z0-9]*".regex()
fun parseIdentifier()
  takePattern(identifierRegex)

fun bracket(p1, p2, p3)
  p1()
  val x = p2()
  p3()
  x

val charRegex = r"^#\\[^\r\n\t\) ]+".regex()
fun parseChar()
  val x = takePattern(charRegex)
  SChar(x.slice.advance(2).string)

val symbolRegex = "^([^.#; \\]\\t\\r\\n()',`\"][^; \\t\\r\\n()',`\"]*|[.][^; \\t\\r\\n()',`\"\\]]+)".regex()
fun parseSymbol()
  SSymbol(takePattern(symbolRegex))

val boolRegex = r"^#[ft]".regex();
fun parseBool()
  SBool("#t" == takePattern(boolRegex))

fun parseNum()
  SNumber(parseFloat())

val openListRegex = r"^[([{]".regex()
val closeListRegex = r"^[)\]}]".regex()
val whitespace = r"^[\n\r\t ]+".regex()

fun parseWhitespace()
  takePattern(whitespace)

fun parseOpenList()
  takePattern(openListRegex)

fun parseCloseList()
  takePattern(closeListRegex)

fun parseCells(): <div,exn,parse<string>> sexpr
  val x = many(parseAtom)
  match optional({text(".")})
    Just(_) ->
      optional(parseWhitespace)
      val x2 = parseAtom()
      SList(x, Just(x2))
    Nothing -> SList(x, Nothing)

fun parseList()
  bracket(parseOpenList, fn() parseCells(), parseCloseList)

fun parseAtom(): <div,exn,parse<string>> token
  val x = ors([tokenize(parseList),tokenize(parseNum),tokenize(parseBool),tokenize(parseSymbol),{fail(Expected("Atom", Position(offset())))}])
  optional(parseWhitespace)
  x

fun parseComplete(p: parser<r,a,e>): <> parser<r,a,e>
  fn()
    val x = p()
    parseEndOfInput()
    x

fun tokenize(p: parser<r,sexpr,e>): <> parser<r,token,e>
  fn()
    val start = offset()
    val x = p()
    val end = offset()
    Token(x, start, end)

fun parseTest(parser, input, showX): <console,exn,div> ()
  val result = parseComplete(parser).run(input)
  match result
    Right(x) -> println("Success: " ++ showX(x))
    Left(err) -> println("Error: " ++ err.show(fn(x: string) x, input))

fun main()
  parseTest(parseNum, "1.53", fn(x) show(x))
  parseTest(parseChar, r"#\newline", fn(x) show(x))
  parseTest(parseBool, "#t", fn(x) show(x))
  parseTest(parseIdentifier, "x", fn(x) show(x))
  parseTest(parseSymbol, "+", fn(x) show(x))
  parseTest(parseList, "(+)", fn(x) show(x))
  parseTest(parseList, "(+ 3 5)", fn(x) show(x))
  parseTest(parseList, "[+ 3 5]", fn(x) show(x))
  parseTest(parseList, "{+ 3 5 . (list a b c)}", fn(x) show(x))

  
import newstd/text/parse
import std/text/regex
import std/num/float64

type sexpr
  SBool(b: bool)
  SChar(c: string)
  SSymbol(s: string)
  SNumber(n: float64)
  SList(l: list<sexpr>, r: maybe<sexpr>)

fun show(s: sexpr): <> string
  match s
    SBool(b) -> if b then "#t" else "#f"
    SChar(c) -> r"#\" ++ c
    SSymbol(s1) -> "s" ++ s1
    SNumber(n) -> "n" ++ n.show()
    SList(l, Nothing) -> "(" ++ l.map(fn(x) show(x.unsafe-decreasing)).join(" ") ++ ")"
    SList(l, Just(r)) -> "(" ++ l.map(fn(x) show(x.unsafe-decreasing)).join(" ") ++ " . " ++ show(r.unsafe-decreasing) ++ ")"

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

val symbolRegex = "^([^.#; \\t\\r\\n()',`\"][^; \\t\\r\\n()',`\"]*|[.][^; \\t\\r\\n()',`\"]+)".regex()
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
  trace("Here")
  trace(x.show-list(show))
  SList(x, Nothing)
  // match optional({token(".")})
  //   Just(_) ->
  //     trace("Here")
  //     // parseWhitespace()
  //     val x2 = parseAtom()
  //     SList(x, Just(x2))
  //   Nothing -> SList(x, Nothing)

fun parseList()
  bracket(parseOpenList, fn() parseCells(), parseCloseList)

fun parseAtom(): <div,exn,parse<string>> sexpr
  parseWhitespace()
  ors([parseList,parseNum,parseBool,parseSymbol])

fun parseComplete(p: parser<r,a,e>): <> parser<r,a,e>
  fn()
    val x = p()
    parseEndOfInput()
    x
  
fun parseTest(parser, input, showX): <console,exn,div> ()
  val result = parseComplete(parser).run(input)
  match result
    Right(x) -> println("Success: " ++ showX(x))
    Left(err) -> println("Error: " ++ err.show(fn(x: string) x))

fun main()
  parseTest(parseNum, "1.53", fn(x) show(x))
  parseTest(parseChar, r"#\newline", fn(x) show(x))
  parseTest(parseBool, "#t", fn(x) show(x))
  parseTest(parseIdentifier, "x", fn(x) show(x))
  parseTest(parseSymbol, "+", fn(x) show(x))
  parseTest(parseList, "(+)", fn(x) show(x))
  // parseTest(parseList, "(+ 3 5)", fn(x) show(x))
  // parseTest(parseList, "[+ 3 5]", fn(x) show(x))
  // parseTest(parseList, "{+ 3 5 . (list a b c)}", fn(x) show(x))

  
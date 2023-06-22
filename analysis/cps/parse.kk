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
  SString(s: string)
  SSymbol(s: string)
  SNumber(n: float64)
  SList(l: list<token>, r: maybe<token>)
  SQuote(t: token)
  SQuasiquote(t: sexpr)
  SUnquote(t: token)
  SUnquoteSplicing(t: token)
  SSplice(t: sexpr)

type program
  Program(l: list<token>)

fun show(p: program): div string
  p.l.map(show).join("\n")

fun show(t: token): div string
  show(t.value)

fun show(s: sexpr): div string
  match s
    SBool(b) -> if b then "#t" else "#f"
    SChar(c) -> r"#\" ++ c
    SString(s1) -> "\"" ++ s1 ++ "\""
    SSymbol(s1) -> s1
    SNumber(n) -> n.show()
    SList(l, Nothing) -> "(" ++ l.map(show).join(" ") ++ ")"
    SList(l, Just(r)) -> "(" ++ l.map(show).join(" ") ++ " . " ++ show(r) ++ ")"
    SQuote(t) -> "'" ++ show(t)
    SQuasiquote(t) -> "`" ++ show(t)
    SUnquote(t) -> "," ++ show(t)
    SUnquoteSplicing(t) -> ",@" ++ show(t)
    SSplice(t) -> "@" ++ show(t)

fun bracket(p1, p2, p3)
  p1()
  val x = p2()
  p3()
  x

val stringRegex = "^\"[^\"]*\"".regex()
fun parseString()
  val x = takePattern(stringRegex)
  val s = x.slice()
  SString(s.substr(1, x.count() - 1).string)

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

fun parseQuote()
  text("'")
  SQuote(parseAtom())

fun parseQuasiquote()
  text("`")
  SQuasiquote(parseList())

fun parseUnquoteSplicing()
  text(",@")
  SUnquoteSplicing(parseAtom())

fun parseUnquote()
  text(",")
  SUnquote(parseAtom())

fun parseSplice()
  text("@")
  SSplice(parseList())

fun parseAtom()
  val x = ors([
    tokenize(parseList),
    tokenize(parseNum),
    tokenize(parseChar),
    tokenize(parseString),
    tokenize(parseBool),
    // tokenize(parseLiteralVector),
    tokenize(parseSymbol),
    tokenize(parseQuote),
    tokenize(parseQuasiquote),
    tokenize(parseUnquoteSplicing),
    tokenize(parseUnquote),
    tokenize(parseSplice),
    {fail(Expected("Atom", Position(offset())))}])
  optional(parseWhitespace)
  x

fun parseToEof(p: parser<r,a,e>): <> parser<r,a,e>
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

fun parseProgram()
  optional(parseWhitespace)
  val p = Program(many(parseAtom))
  parseEndOfInput()
  p

fun parseTest(parser, input, showX): <console,exn,div> ()
  val result = parser.run(input)
  match result
    Right(x) -> println("Success: " ++ showX(x))
    Left(err) -> println("Error: " ++ err.show(fn(x: string) x, input))

val programs = [
r"
(defun fact (n)
     (if (< n 2)
         1
         (* n (fact (1- n)))))
         ",
r"(define fact
     (lambda (n)
       (if (< n 2)
           1
         (* n (fact (- n 1))))))",
r"(defun fact (n)
     (labels ((tail-recursive-fact (counter accumulator)
                (if (> counter n)
                    accumulator
                    (tail-recursive-fact (1+ counter)
                                         (* counter accumulator)))))
       (tail-recursive-fact 1 1)))",
r"(define fact
     (λ (n)
       (letrec ((tail-recursive-fact
                 (λ (counter accumulator)
                   (if (> counter n)
                       accumulator
                     (tail-recursive-fact (+ counter 1)
                                          (* counter accumulator))))))
               (tail-recursive-fact 1 1))))",
r"(define fact
     (λ (n)
       (let loop ((counter n)
                  (accumulator 1))
            (if (< counter 2)
                accumulator
              (loop (- counter 1)
                    (* accumulator counter))))))",
r"(lambda ,(lambda->formals exp))",                    

]


fun main()
  parseTest(parseNum, "1.53", show)
  parseTest(parseChar, r"#\newline", show)
  parseTest(parseBool, "#t", show)
  parseTest(parseSymbol, "+", show)
  parseTest(parseString, "\"Hello\"", show)
  parseTest(parseList, "(+)", show)
  parseTest(parseList, "(+ 3 5)", show)
  parseTest(parseList, "[+ 3 5]", show)
  parseTest(parseList, "{+ 3 5 . (list a b c)}", show)
  programs.foreach fn(p)
    parseTest(parseProgram, p, show)
  
import newstd/text/parse
import std/text/regex
import std/os/path
import std/os/file
import std/os/dir
import std/num/float64

value struct position
  start: int
  end: int

type sexpr
  SBool(b: bool, pos: position = Position(-1, -1))
  SChar(c: string, pos: position = Position(-1, -1))
  SString(s: string, pos: position = Position(-1, -1))
  SSymbol(s: string, pos: position = Position(-1, -1))
  SNumber(n: float64, pos: position = Position(-1, -1))
  SList(l: list<sexpr>, r: maybe<sexpr>, pos: position = Position(-1, -1))
  SQuote(e: sexpr, pos: position = Position(-1, -1))
  SQuasiquote(e: sexpr, pos: position = Position(-1, -1))
  SUnquote(e: sexpr, pos: position = Position(-1, -1))
  SUnquoteSplicing(e: sexpr, pos: position = Position(-1, -1))
  SSplice(e: sexpr, pos: position = Position(-1, -1))
  SVector(e: list<sexpr>, pos: position=Position(-1, -1))

fun updatePos(s: sexpr, p: position)
  match s
    SBool(b, _) -> SBool(b, p)
    SChar(c, _) -> SChar(c, p)
    SString(s1, _) -> SString(s1, p)
    SSymbol(s1, _) -> SSymbol(s1, p)
    SNumber(n, _) -> SNumber(n, p)
    SList(l, r, _) -> SList(l, r, p)
    SQuote(e, _) -> SQuote(e, p)
    SQuasiquote(e, _) -> SQuasiquote(e, p)
    SUnquote(e, _) -> SUnquote(e, p)
    SUnquoteSplicing(e, _) -> SUnquoteSplicing(e, p)
    SSplice(e, _) -> SSplice(e, p)
    SVector(e, _) -> SVector(e, p)

type program
  Program(terms: list<sexpr>)

fun show(p: program): div string
  p.terms.map(show).join("\n")

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
    SVector(l) -> "#(" ++ l.map(show).join(" ") ++ ")"

fun bracket(p1, p2, p3)
  p1()
  val x = p2()
  p3()
  x


fun tokenizer(p)
  val start = offset()
  val x = p()
  val end = offset()
  x.updatePos(Position(start, end))

val stringRegex = "^\"[^\"]*\"".regex()
fun parseString()
  with tokenizer
  val x = takePattern(stringRegex)
  val s = x.slice()
  SString(s.substr(1, x.count() - 1).string)

val charRegex = r"^#\\[^\r\n\t\) ]+".regex()
fun parseChar()
  with tokenizer
  val x = takePattern(charRegex)
  SChar(x.slice.advance(2).string)

val symbolRegex = "^([^.#; \\]\\t\\r\\n()',`\"][^; \\]\\t\\r\\n()',`\"]*|[.][^; \\t\\r\\n()',`\"\\]]+)".regex()
fun parseSymbol()
  with tokenizer
  SSymbol(takePattern(symbolRegex))

val boolRegex = r"^#[ftFT]".regex();
fun parseBool()
  with tokenizer
  val v = takePattern(boolRegex)
  SBool("#t" == v || "#T" == v)

fun parseNum()
  with atomic
  with tokenizer
  SNumber(parseFloat())

val commentRegex = r"^;[^\n\r]*".regex()
fun parseComment()
  takePattern(commentRegex)

val openListRegex = r"^[([{]".regex()
val closeListRegex = r"^[)\]}]".regex()
val whitespace = r"^[\n\r\t ]+".regex()

val whiteChars = ['\n','\t',' ','\r']
fun parseWhite()
  many({takeOneOf(whiteChars)}).string

fun parseWhitespace()
  many({parseWhite.or(parseComment)})

fun parseOpenList()
  takePattern(openListRegex)

fun parseCloseList()
  takePattern(closeListRegex)

fun parseCells()
  optional(parseWhitespace)
  val x = many(parseAtom)
  optional(parseWhitespace)
  match optional({text(".")})
    Just(_) ->
      optional(parseWhitespace)
      val x2 = parseAtom()
      SList(x, Just(x2))
    Nothing -> SList(x, Nothing)

fun parseVector()
  with tokenizer
  text("#(")
  optional(parseWhitespace)
  val x = many(parseAtom)
  optional(parseWhitespace)
  text(")")
  SVector(x)

fun parseList()
  with tokenizer
  bracket(parseOpenList, parseCells, parseCloseList)

fun parseQuote()
  with tokenizer
  text("'")
  SQuote(parseAtom())

fun parseQuasiquote()
  with tokenizer
  text("`")
  SQuasiquote(parseList())

fun parseUnquoteSplicing()
  with tokenizer
  text(",@")
  SUnquoteSplicing(parseAtom())

fun parseUnquote()
  with tokenizer
  text(",")
  SUnquote(parseAtom())

fun parseSplice()
  with tokenizer
  text("@")
  SSplice(parseList())

fun parseAtom()
  val x = ors([
    parseList,
    parseNum,
    parseChar,
    parseString,
    parseBool,
    parseVector,
    parseSymbol,
    parseQuote,
    parseQuasiquote,
    parseUnquoteSplicing,
    parseUnquote,
    parseSplice,
    {fail(Expected("Atom", offset()))}])
  optional(parseWhitespace)
  x

fun parseProgram()
  optional(parseWhitespace)
  val p = Program(many(parseAtom))
  optional(parseWhitespace)
  parseEndOfInput()
  p

fun parseTest(parser, input, showX, file="None")
  val result = parser.run(input)
  match result
    Right(x) -> 
      showX(x)
      println("Success: ")
    Left(err) -> println("Error: " ++ err.show(fn(x: string) x, input) ++ " in file " ++ file)

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
  // parseTest(parseNum, "1.53", show)
  // parseTest(parseChar, r"#\newline", show)
  // parseTest(parseBool, "#t", show)
  // parseTest(parseSymbol, "+", show)
  // parseTest(parseString, "\"Hello\"", show)
  // parseTest(parseList, "(+)", show)
  // parseTest(parseList, "(+ 3 5)", show)
  // parseTest(parseProgram, "[+ 3 5]", show)
  // parseTest(parseList, "{+ 3 5 . (list a b c)}", show)
  
  // programs.foreach fn(p)
  //   parseTest(parseProgram, p, show)
  list-directory-recursive("/Users/timwhiting/koka_code/higher-order-programs/scheme".path).foreach fn(p)
    if is-file(p) then // nbody
      if p.show.ends-with(".scm\"").is-just then
        parseTest(parseProgram, read-text-file(p), show, p.show)

// TODO: Emit tokens including all whitespace etc. Let AST include token references.
// Really should add macros to Koka so we can dynamically create an AST with tokens for each constructor
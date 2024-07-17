import newstd/text/parse
import std/data/linearmap
import std/text/regex
import std/os/path
import std/os/file
import std/os/dir
import std/num/float64
import std/core/undiv

pub value struct position
  start: int
  end: int

pub type sexpr
  SBool(b: bool, pos: position = Position(-1, -1))
  SChar(c: string, pos: position = Position(-1, -1))
  SString(s: string, pos: position = Position(-1, -1))
  SName(s: string, pos: position = Position(-1, -1))
  SNumber(n: float64, pos: position = Position(-1, -1))
  SCons(l: sexpr, r: sexpr, pos: position = Position(-1, -1))
  SNil(pos: position = Position(-1, -1))

val sQuote = SName("quote")
val sQuasiquote = SName("quasiquote")
val sUnquote = SName("unquote")
val sUnquoteSplicing = SName("unquote-splicing")
val sSplice = SName("splice")
val sCons = SName("cons")
val sList = SName("list")
val sAppend = SName("append")
val sDefine = SName("define")
val sLambda = SName("lambda")
val sLambday = SName("λ")
val sLet = SName("let")
val sLetStar = SName("let*")
val sLetRec = SName("letrec")
val sSetBang = SName("set!")
val sBegin = SName("begin")
val sVoid = SName("void")
val sIf = SName("if")
val sIfZero = SName("if-zero")
val sCond = SName("cond")
val sElse = SName("else")
val sRightArrow = SName("=>")
val sAnd = SName("and")
val sOr = SName("or")
val sValues = SName("values")
val sLetValues = SName("let-values")
val sVector = SName("vectorLiteral")

fun updatePos(s: sexpr, p: position)
  match s
    SBool(b) -> SBool(b, p)
    SChar(c) -> SChar(c, p)
    SString(s1) -> SString(s1, p)
    SName(s1) -> SName(s1, p)
    SNumber(n) -> SNumber(n, p)
    SCons(l, r) -> SCons(l, r, p)
    SNil() -> SNil(p)

pub alias sprogram = list<sexpr>

pub fun sprog/show(p: sprogram): div string
  p.map(show).join("\n")

pub fun toList(s: sexpr): pure list<sexpr>
  match s
    SCons(car, cdr) -> Cons(car, cdr.pretend-decreasing.toList)
    SNil() -> []
    _ -> throw("toList not implemented for " ++ s.show) 

pub fun toDottedList(s: sexpr): (list<sexpr>, sexpr)
  match s
    SCons(car, cdr) -> 
      val (lst, end) = cdr.pretend-decreasing.toDottedList
      (Cons(car, lst), end)
    _ -> ([], s)

pub fun sexpr/show(s: sexpr): div string
  match s
    SBool(b) -> if b then "#t" else "#f"
    SChar(c) -> r"#\" ++ c
    SString(s1) -> "\"" ++ s1 ++ "\""
    SName(s1) -> s1
    SNumber(n) -> n.show()
    SNil() -> "()"
    SCons() ->
      match s.toDottedList
        (l, SNil()) -> "(" ++ l.map(show).join(" ") ++ ")"
        (l, end) -> "(" ++ l.map(show).join(" ") ++ " . " ++ show(end) ++ ")"

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
  SName(takePattern(symbolRegex))

val boolRegex = r"^#[ftFT]".regex();
fun parseBool()
  with tokenizer
  val v = takePattern(boolRegex)
  SBool("#t" == v || "#T" == v)

fun parseNum()
  with atomic
  with tokenizer
  SNumber(parseFloat())

val commentRegex = r"^;[^\n]*".regex()
fun parseComment()
  takePattern(commentRegex)

val openListRegex = r"^[([{]".regex()
val closeListRegex = r"^[)\]}]".regex()
val whitespace = r"^[\n\r\t ]+".regex()

fun parseWhitespace()
  many1({(fn() takePattern(whitespace)).or(parseComment)})

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
      mklist(x, Just(x2))
    Nothing -> mklist(x, Nothing)

fun mklist(l: list<sexpr>, m: maybe<sexpr> = Nothing): sexpr
  match l
    Nil -> m.default(SNil())
    Cons(h, t) -> SCons(h, mklist(t.pretend-decreasing, m)) 

fun isList(s: sexpr): bool
  match s
    SNil() -> True
    SCons(_, b) -> b.isList
    _ -> False

fun parseVector()
  with tokenizer
  text("#(")
  optional(parseWhitespace)
  val x = many(parseAtom)
  optional(parseWhitespace)
  text(")")
  mklist(Cons(sVector, x))

fun parseList()
  with tokenizer
  bracket(parseOpenList, parseCells, parseCloseList)

fun parseQuote()
  with tokenizer
  text("'")
  mklist([sQuote, parseAtom()])

fun parseQuasiquote()
  with tokenizer
  text("`")
  mklist([sQuasiquote, parseList()])

fun parseUnquoteSplicing()
  with tokenizer
  text(",@")
  mklist([sUnquoteSplicing, parseAtom()])

fun parseUnquote()
  with tokenizer
  text(",")
  mklist([sUnquote, parseAtom()])

fun parseSplice()
  with tokenizer
  text("@")
  mklist([sSplice, parseList()])

fun parseAtom(): <div,parse<string>> sexpr
  val x = ors([
    parseList,
    parseNum,
    parseChar,
    parseString,
    parseBool,
    parseSymbol,
    parseVector,
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
  val p = many(parseAtom)
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


fun parseFile(f: string): io list<sexpr>
  parseProgramFromString(read-text-file(f.path))

fun parseProgramFromString(s: string): pure list<sexpr>
  match parseProgram.run(s)
    Right(x) -> x
    Left(err) -> throw(err.show(fn(x: string) x, s))

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

fun (==)(s1: sexpr, s2: sexpr): bool
  match (s1, s2)
    (SBool(b1), SBool(b2)) -> b1 == b2
    (SNumber(n1), SNumber(n2)) -> n1 == n2
    (SChar(c1), SChar(c2)) -> c1 == c2
    (SString(s1), SString(s2)) -> s1 == s2
    (SName(n1), SName(n2)) -> n1 == n2
    (SNil(), SNil()) -> True
    (SCons(h1, t1), SCons(h2, t2)) -> (==)(h1.pretend-decreasing, h2.pretend-decreasing) && (==)(t1.pretend-decreasing, t2.pretend-decreasing)
    _ -> False

alias nameMap = some<e> linearMap<string,int>
val globalNameGen:ref<global,nameMap> = pretend-total{ref(LinearMap([]))}
fun genName(n: string): sexpr
  pretend-total
    val m = !globalNameGen
    val newM = m.update(n, 1, fn(x, _) x + 1)
    globalNameGen.set(newM)
    SName(n ++ newM.getDefault(n, 0).show)
// fun main()
//   parseTest(parseNum, "1.53", show)
//   parseTest(parseChar, r"#\newline", show)
//   parseTest(parseBool, "#t", show)
//   parseTest(parseSymbol, "+", show)
//   parseTest(parseString, "\"Hello\"", show)
//   parseTest(parseList, "(+)", show)
//   parseTest(parseList, "(+ 3 5)", show)
//   parseTest(parseProgram, "[+ 3 5]", show)
//   parseTest(parseList, "{+ 3 5 . (list a b c)}", show)
//   val p = "/Users/timwhiting/koka_code/higher-order-programs/scheme/r6rs/nbody.scm".path
//   parseTest(parseProgram, read-text-file(p), show, p.show)
//   programs.foreach fn(p)
//     parseTest(parseProgram, p, show)
//   list-directory-recursive("/Users/timwhiting/koka_code/higher-order-programs/scheme".path).foreach fn(p)
//     if is-file(p) then // nbody
//       if p.show.ends-with(".scm\"").is-just then
//         parseTest(parseProgram, read-text-file(p), show, p.show)

// TODO: Emit tokens including all whitespace etc. Let AST include token references.
// Really should add macros to Koka so we can dynamically create an AST with tokens for each constructor
import compiler/lib/printer
import std/os/path
import std/os/file

pub infixr 5 (/), (||), (|-|), (|--|) 
pub infixr 6 (|.|), (|+|)

// List, tupled and semiBraces pretty print a list of documents
// either horizontally or vertically aligned.

fun list(l: list<doc>): doc
  encloseSep(l, lbracket, rbracket, comma)

fun tupled(l: list<doc>): doc
  l.encloseSep(lparen, rparen, text(", "))

fun semiBraces(l: list<doc>): doc
  l.encloseSep(lbrace, rbrace, semi)

fun angled(l: list<doc>): doc
  l.encloseSep(langle, rangle, comma)

fun encloseSep(lst: list<doc>, l: doc, r: doc, p: doc): doc
  match lst
    Nil -> l |.| r
    Cons(c, Nil) -> l |.| c |.| r
    _ -> 
      val x = l |.| lst.punctuate(p).hcat |.| r
      x.nest(2) 

fun punctuate(l: list<doc>, p: doc): list<doc>
  match l
    Nil -> Nil
    Cons(c, Nil) -> Cons(c, Nil)
    Cons(c, cs) -> Cons(c |.| p, punctuate(cs, p)) 

// High level combinators
fun sep(l: list<doc>): doc
  l.vsep.group

fun fillSep(l: list<doc>): doc
  l.fold((/))

fun hsep(l: list<doc>): doc
  l.fold((|+|))

fun vsep(l: list<doc>): doc
  l.filter(fn(x) !x.is-empty).fold((|--|))

fun cat(l: list<doc>): doc
  l.vcat.group

fun fillCat(l: list<doc>): doc
  l.fold((||))

fun hcat(l: list<doc>): doc
  l.fold((|.|))

fun vcat(l: list<doc>): doc
  l.filter(fn(x) !x.is-empty).fold((||))

fun fold(l: list<doc>, f: (doc, doc) -> doc): doc
  match l
    Nil -> empty
    Cons(x, xs) -> xs.foldr(x, f)

fun (|.|)(x: doc, y: doc): doc
  x.beside(y)

fun (|+|)(x: doc, y: doc): doc
  x |.| space |.| y

fun (/)(x: doc, y: doc): doc
  if x.is-empty then y else if y.is-empty then x else x |.| softline |.| y

fun (||)(x: doc, y: doc): doc
  x |.| softbreak |.| y

fun (|-|)(x: doc, y: doc): doc
  if x.is-empty then y else if y.is-empty then x else x |.| line |.| y

fun (|--|)(x: doc, y: doc): doc
  x |.| linebreak |.| y

val softline = line.group
val softbreak = linebreak.group

fun squotes(d: doc): doc
  d.enclose(squote, squote)

fun dquotes(d: doc): doc
  d.enclose(dquote, dquote)

fun braces(d: doc): doc
  d.enclose(lbrace, rbrace)

fun parens(d: doc): doc
  d.enclose(lparen, rparen)

fun angles(d: doc): doc
  d.enclose(langle, rangle)

fun brackets(d: doc): doc
  d.enclose(lbracket, rbracket)

fun enclose(x: doc, l: doc, r: doc): doc
  l |.| x |.| r

val lparen = Char('(')
val rparen = Char(')')
val langle = Char('<')
val rangle = Char('>')
val lbrace = Char('{')
val rbrace = Char('}')
val lbracket = Char('[')
val rbracket = Char(']')

val squote = Char('\'')
val dquote = Char('"')
val semi = Char(';')
val colon = Char(':')
val comma = Char(',')
val space = Char(' ')
val dot = Char('.')
val backslash = Char('\\')
val equals = Char('=')

// string is like "text" but replaces '\n' by "line"
fun pretty(s: string): doc
  if s == "" then empty else
    match s.starts-with("\n")
      Just(x) -> line |.| pretty(x.string.unsafe-decreasing)
      _ -> 
        val (xs, ys) = span(s.list, fn(c) c != '\n')
        text(xs.string) |.| pretty(ys.string.unsafe-decreasing)

fun pretty(b: bool): doc
  b.show.text

fun pretty(i: int): doc
  i.show.text

fun pretty(d: float64): doc
  d.show.text

// Semi primitive: fill and fillBreak

fun fillBreak(d: doc, f): doc
  d.width(fn(w) if w > f then linebreak.nest(f) else spaces(f - w).text)

fun fill(d: doc, f: int): doc
  d.width(fn(w) if w >= f then empty else spaces(f - w).text)

fun width(d: doc, f: (int -> doc)): doc
  column(fn(k1) d |.| column(fn(k2) f(k1 - k2)))

// Semi primitive: Alignment and indentation

fun indent(d: doc, i: int): doc
  (spaces(i).text |.| d).hang(i)

fun hang(d: doc, i: int): doc
  d.nest(i).align()

fun align(d: doc): doc
  column(fn(k1:int) nesting(fn(i1) d.nest(k1 - i1)))

// primitives

alias docs = list<doc>
type doc
  Empty
  Char(c: char) // char cannot be \n
  Text(s: string) // text does not contain \n
  Line(b: bool) // True when undone by group, do not insert a space
  Cat(d1: doc, d2: doc)
  Nest(i: int, d: doc)
  Union(d1: doc, d2: doc) // invariant: first lines of first doc longer than the first lines of the second doc
  Column(f: int -> doc)
  Nesting(f: int -> doc)
  Colored(b: bool, c: color, d: doc)
  ColoredEnd

type simpleDoc
  SEmpty
  SChar(i: int, c: char, d: simpleDoc)
  SText(i: int, s: string, d: simpleDoc)
  SLine(i: int, d: simpleDoc)
  SColorOpen(b: bool, c: color, d: simpleDoc)
  SColorClose(d: simpleDoc)


val empty = Empty

fun char(c: char): doc
  if c == '\n' then line else Char(c)

fun text(s: string): doc
  if s == "" then empty else Text(s)

val line = Line(False)
val linebreak = Line(True)

fun beside(x: doc, y: doc): doc
  if x.is-empty then y else if y.is-empty then x else Cat(x, y)

fun nest(x: doc, i: int): doc
  Nest(i, x)

fun column(f: int -> doc): doc
  Column(f)

fun nesting(f: int -> doc): doc
  Nesting(f)

fun group(d: doc): doc
  Union(d.flatten, d)

fun color(d: doc, c: color): doc
  Colored(True, c, d)

fun bcolor(d: doc, c: color): doc
  Colored(False, c, d)

fun flatten(d: doc): doc
  match d
    Cat(x, y) -> Cat(flatten(x), flatten(y))
    Nest(i, x) -> Nest(i, flatten(x))
    Line(b) -> if b then Empty else Text(" ")
    Union(x, _) -> flatten(x)
    Column(f) -> Column(fn(x) flatten(f(x)))
    Nesting(f) -> Nesting(fn(x) flatten(f(x)))
    Colored(b, c, x) -> Colored(b, c, flatten(x))
    x -> x

fun dcontains(d: doc, p: (string -> e bool)): e bool
  d.texts.any(p)

fun dStartsWith(d: doc, s: string): bool
  dStartsWithT(d.texts, s, s.count)

fun dStartsWithT(l: list<string>, pre: string, n: int)
  match l
    Nil -> n == 0
    Cons(s, xs) ->
      val m = s.count
      if m >= n then
        s.slice.take(n).string == pre
      else
        pre.slice.take(m).string == s && dStartsWithT(xs, pre.slice.subslice(m,pre.count).string, n - m)

// TODO: Optimize a bunch of this
fun dEndsWith(d: doc, s: string): bool
  dEndsWithT(d.rtexts, s.list.reverse.string, s.count)

fun dEndsWithT(l:list<string>, rpost: string, n:int)
  match l
    Nil -> n == 0
    Cons(s, xs) ->
      val m = s.count
      if m >= n then
        s.slice.take(n).string == rpost
      else
        rpost.slice.take(m).string == s && dEndsWithT(xs, rpost.slice.subslice(m,rpost.count).string, n - m)

fun texts(d: doc): list<string>
  match d
    Empty -> []
    Char(c) -> [c.show-char]
    Text(s) -> [s]
    Line(br) -> if br then [] else ["\n"]
    Union(x, _) -> x.texts
    Cat(x, y) -> x.texts ++ y.texts
    Nest(_, x) -> x.texts
    Column(f) -> f(0).texts
    Nesting(f) -> f(0).texts
    Colored(_, _, x) -> x.texts
    ColoredEnd -> []

fun rtexts(d: doc): list<string> // reversed text fragments
  match d
    Empty -> []
    Char(c) -> [c.show-char]
    Text(s) -> [s.list.reverse.string]
    Line(br) -> if br then [] else ["\n"]
    Union(x, _) -> x.rtexts
    Cat(x, y) -> x.rtexts ++ y.rtexts
    Nest(_, x) -> x.rtexts
    Column(f) -> f(0).rtexts
    Nesting(f) -> f(0).rtexts
    Colored(_, _, x) -> x.rtexts
    ColoredEnd -> []

// renderers
fun (==)(d1: doc, d2: doc): bool
  d1.renderCompact.displayS == d2.renderCompact.displayS

// renderPretty: the default pretty printing algorithm

// list of indentation/document pairs; saves an indirection over list<(int, doc)>
type docList
  DocNil
  DocCons(i: int, d: doc, dl: docList)

fun renderPrettyB(rfrac: float64, w: int, xdoc: doc): div string
  // r - the ribbon width in characters
  val r = max(0, min(w, (w.float64 * rfrac).int))

  // r = ribbon with, w = page width, n = indentation of current line, k = current column
  // x and y, the (simple) documents to chose from.
  // precondition: first lines of x are longer than the first lines of y
  fun nicest(n, k, x, y)
    x // TODO: reimplement this according to renderPretty

  // b = base nesting, n = indentation of current line, k = current column
  // (k >= n) && (k - n == count of inserted characters)
  fun best(b, n, k, l)
    match l
      Nil -> ""
      Cons((i, d), ds) ->
        match d
          Empty -> best(b, n, k, ds)
          Char(c) -> c.show-char ++ best(b, n, k + 1, ds)
          Text(s) -> s.show ++ best(b, n, k + s.count, ds)
          Line -> "\n" ++ best(b, i, i, ds)
          Cat(x, y) -> best(b, n, k, Cons((i, x), Cons((i, y), ds)))
          Nest(j, x) ->
            val i' = i + j
            best(if b == 0 then i' else b, n, k, Cons((i', x), ds))
          Union(x, y) -> nicest(n, k, best(b, n, k, Cons((i, x), ds)), best(b, n, k, Cons((i, y), ds)))
          Column(f) -> best(b, n, k, Cons((i, f(k)), ds))
          Nesting(f) -> best(b, n, k, Cons((i, f(i)), ds))
          Colored(_, _, x) -> best(b, n, k, Cons((i, x), ds))
          ColoredEnd -> best(b, n, k, ds)
  best(0, 0, 0, [(0, xdoc)])

fun renderPretty(rfrac: float64, w: int, xdoc: doc): div simpleDoc
  // r - the ribbon width in characters
  val r = max(0, min(w, (w.float64 * rfrac).int))

  // r = ribbon with, w = page width, n = indentation of current line, k = current column
  // x and y, the (simple) documents to chose from.
  // precondition: first lines of x are longer than the first lines of y
  fun nicest(n, k, x, y)
    val width = min(w - k, r - k + n)
    if fits(width, x) then x else y

  // b = base nesting, n = indentation of current line, k = current column
  // (k >= n) && (k - n == count of inserted characters)
  fun best(b, n, k, l)
    match l
      Nil -> SEmpty
      Cons((i, d), ds) ->
        match d
          Empty -> best(b, n, k, ds)
          Char(c) -> SChar(b, c, best(b, n, k + 1, ds))
          Text(s) -> SText(b, s, best(b, n, k + s.count, ds))
          Line -> SLine(i, best(b, i, i, ds))
          Cat(x, y) -> best(b, n, k, Cons((i, x), Cons((i, y), ds)))
          Nest(j, x) ->
            val i' = i + j
            best(if b == 0 then i' else b, n, k, Cons((i', x), ds))
          Union(x, y) -> nicest(n, k, best(b, n, k, Cons((i, x), ds)), best(b, n, k, Cons((i, y), ds)))
          Column(f) -> best(b, n, k, Cons((i, f(k)), ds))
          Nesting(f) -> best(b, n, k, Cons((i, f(i)), ds))
          Colored(f, c, x) -> SColorOpen(f, c, best(b, n, k, Cons((i, x), Cons((i, ColoredEnd), ds))))
          ColoredEnd -> SColorClose(best(b, n, k, ds))
  best(0, 0, 0, [(0, xdoc)])

fun fits(w: int, x: simpleDoc)
  if w < 0 then False
  else match x
    SEmpty -> True
    SChar(_, _, x) -> fits(w - 1, x)
    SText(_, s, x) -> fits(w - s.count, x)
    SLine(_, _) -> True
    SColorOpen(_, _, x) -> fits(w, x)
    SColorClose(x) -> fits(w, x)

// renderCompact: renders documents without indentation
// fast and fewer characters output, good for machines
fun renderCompact(xdoc: doc): simpleDoc
  fun scan(k, l)
    match l
      Nil -> SEmpty
      Cons(d, ds) ->
        match d
          Empty -> scan(k, ds)
          Char(c) -> SChar(0, c, scan(k + 1, ds.unsafe-decreasing))
          Text(s) -> SText(0, s, scan(k + s.count, ds.unsafe-decreasing))
          Line() -> SLine(0, scan(0, ds.unsafe-decreasing))
          Cat(x, y) -> scan(k, Cons(x, Cons(y, ds)).unsafe-decreasing)
          Nest(_, x) -> scan(k, Cons(x, ds).unsafe-decreasing)
          Union(_, y) -> scan(k, Cons(y, ds).unsafe-decreasing)
          Column(f) -> scan(k, Cons(f(k), ds).unsafe-decreasing)
          Nesting(f) -> scan(k, Cons(f(0), ds).unsafe-decreasing)
          Colored(f, c, x) -> SColorOpen(f, c, scan(k, Cons(x, Cons(ColoredEnd, ds)).unsafe-decreasing))
          ColoredEnd -> SColorClose(scan(k, ds.unsafe-decreasing))
  scan(0, [xdoc])

fun asString(d: doc)
  displayS(renderCompact(d))

// Displayers: displayS and displayIO

fun displayS(simple: simpleDoc): string
  match simple
    SEmpty -> ""
    SChar(_, c, x) -> c.show-char ++ x.displayS
    SText(_, s, x) -> s ++ x.displayS
    SLine(i, x) -> "\n" ++ spaces(i) ++ x.displayS
    SColorOpen(_, _, x) -> x.displayS
    SColorClose(x) -> x.displayS

fun isSpace(c: char): bool
  c == ' ' || c == '\t'

fun skipSpaces(simple: simpleDoc): simpleDoc
  match simple
    SChar(_, c, x) | c.isSpace -> skipSpaces(x)
    SText(i, s, x) ->
      val noSpaces = s.list.drop-while(isSpace).string
      if noSpaces == "" then
        skipSpaces(x)
      else
        SText(i, noSpaces, x)
    _ -> simple 

fun displayP(w: int, simple: simpleDoc): <printer,colorSettings,div> ()
  fun display(curCol, simp, oldSettings)
    match simp
      SEmpty -> ()
      SChar(i, c, x) ->
        if curCol + 1 >= w  && i + 1 < w then
          display(curCol, SLine(i + 1, simp.skipSpaces), oldSettings)
        else
          write(c.show-char)
          display(curCol + 1, x, oldSettings)
      SText(i, s, x) ->
        if curCol + s.count >= w && i + s.count < w then
          display(curCol, SLine(i + 1, simp.skipSpaces), oldSettings)
        else
          write(s)
          display(curCol + s.count, x, oldSettings)
      SLine(i, x) ->
        write-ln("")
        write(spaces(i))
        display(i, x, oldSettings)
      SColorOpen(f, c, x) ->
        val oldSettings' = colorSettings
        if f then 
          with override val colorSettings = oldSettings'(fcolor=c)
          display(curCol, x, oldSettings')
        else
          with override val colorSettings = colorSettings(bcolor=c)
          display(curCol, x, oldSettings')
      SColorClose(x) ->
        with override val colorSettings = oldSettings
        display(curCol, x, oldSettings)
  display(0, simple, colorSettings)

fun writePretty(d: doc)
  displayP(defaultWidth, renderPretty(0.8, defaultWidth, d))

fun writePrettyLn(d: doc)
  writePretty(d |.| linebreak)

fun show(d: doc): div string
  displayS(renderPretty(0.5, defaultWidth, d))

fun putDoc(d: doc)
  println(renderPrettyB(0.5, defaultWidth, d))

fun writeDoc(fpath: path, doc: doc, width: int=defaultWidth)
  fpath.write-text-file(renderPrettyB(0.5, width, doc))

// insert spaces "indentation" used to insert tabs, but tabs seem to cause more trouble than they solve :-)
fun spaces(n: int): string
  match n
    0 -> ""
    1 -> " "
    2 -> "  "
    3 -> "   "
    4 -> "    "
    5 -> "     "
    6 -> "      "
    7 -> "       "
    8 -> "        "
    9 -> "         "
    10 -> "          "
    11 -> "           "
    12 -> "            "
    13 -> "             "
    14 -> "              "
    15 -> "               "
    16 -> "                "
    17 -> "                 "
    _ -> if n <= 0 then "" else replicate(" ", n).join

val defaultWidth = 160

fun test()
  ("test".text |+| "hello".text)
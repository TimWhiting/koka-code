import compiler/lib/printer
import std/os/path
import std/os/file

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


// TODO: More


fun texts(d: doc): list<string>
  match d
    Empty -> []
    Char(c) -> [c.show]
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
    Char(c) -> [c.show]
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
          Char(c) -> c.show ++ best(b, n, k + 1, ds)
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
    SChar(_, c, x) -> c.show ++ x.displayS
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
          write(c.string)
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
  writePretty(d + linebreak)

fun show(d: doc): div string
  displayS(renderPretty(0.5, defaultWidth, d))

fun putDoc(d: doc)
  println(renderPrettyB(0.5, defaultWidth, d))

fun writeDoc(fpath: path, doc: doc, width: int=defaultWidth)
  fpath.write-text-file(renderPrettyB(0.5, width, doc))

// insert spaces "indentation" used to insert tabs, but tabs seem to cause more trouble than they solve :-)
fun spaces(n: int): string
  if n <= 0 then "" else replicate(" ", n).join

val defaultWidth = 160
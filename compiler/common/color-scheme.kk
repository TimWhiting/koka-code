import compiler/lib/printer
import std/core/undiv
// Global color scheme used for pretty printing


// Color Scheme
// Color scheme for the interpreter

effect colorSchemeEffect
  val colors: colorScheme;

fun @default-colorSchemeEff(f)
  handle(f)
    val colors = ColorScheme()

struct colorScheme
  colorInterpreter: color = DarkRed
  colorType: color = DarkCyan
  colorParameter: color = DarkGray
  colorKind: color = ColorDefault
  colorMarker: color = colorInterpreter
  colorError: color = Red
  colorWarning: color = colorError
  colorSource: color = ColorDefault
  colorCommand: color = Red
  colorKeyword: color = DarkYellow
  colorEffect: color = colorType
  colorRange: color = colorInterpreter
  colorSep: color = ColorDefault
  // syntax coloring
  colorComment: color = DarkGreen
  colorReserved: color = DarkYellow
  colorReservedOp: color = ColorDefault
  colorSpecial: color = ColorDefault
  colorString: color = DarkRed
  colorNumber: color = ColorDefault 
  colorModule: color = DarkCyan
  colorCons: color = DarkGreen
  colorTypeCon: color = colorType
  colorTypeVar: color = colorType
  colorTypeKeyword: color = Cyan
  colorTypeKeywordOp: color = colorType
  colorTypeSpecial: color = colorType
  colorTypeParam: color = colorParameter
  colorNameQual: color = ColorDefault

val lightColorScheme = ColorScheme(
  colorNumber = DarkGray,
  colorSource = DarkGray,
  colorCommand = Black,
  colorInterpreter = DarkRed,
  colorError = DarkRed,
  colorWarning = DarkRed,
  colorNameQual = DarkGray,
  colorRange = DarkRed,
  colorMarker = DarkRed,
  colorString = Red
)

fun makeColorScheme(clr: color)
  ColorScheme(clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr,
    clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr, clr)

// Read colors
// Read a comma separated list of name=color pairs.
fun read-color-flags(scheme: colorScheme, s: string)
  fun split(xs: list<char>): list<string>
    val (pre, ys) = xs.span(fn(c) c != ',' && c != ';')
    match ys
      Cons(',', post) -> Cons(pre.string, post.pretend-decreasing.split)
      Cons(';', post) -> Cons(pre.string, post.pretend-decreasing.split)
      Nil -> Cons(pre.string, Nil)
      _ -> [pre.string, ""] // impossible case

  s.list.split.foldl(scheme, fn(sc, s') sc.read-color-flag(s'))

// Read a name=color flag.
fun read-color-flag(scheme: colorScheme, s: string)
  val (name, xs) = s.list.span(fn(c) c != '=' && c != ':')
  match xs
    Cons(c, clr) | c == '=' || c == ':' -> scheme.update(name.string, clr.string)
    _ -> scheme.update(name.string, "default")

fun update(scheme: colorScheme, name: string, color: string)
  val clr = match color
    "black" -> Black
    "darkred" -> DarkRed
    "darkgreen" -> DarkGreen
    "darkyellow" -> DarkYellow
    "darkblue" -> DarkBlue
    "darkmagenta" -> DarkMagenta
    "darkcyan" -> DarkCyan
    "lightgray" -> Gray
    "gray" -> DarkGray
    "red" -> Red
    "green" -> Green
    "yellow" -> Yellow
    "blue" -> Blue
    "cyan" -> Cyan
    "white" -> White
    "default" -> ColorDefault
    // other spellings
    "lightgrey" -> Gray
    "grey" -> DarkGray
    "darkgrey" -> DarkGray
    // other words
    "navy" -> DarkBlue
    "teal" -> DarkCyan
    "maroon" -> DarkRed
    "purple" -> DarkMagenta
    "olive" -> DarkYellow
    "silver" -> Gray
    "lime" -> Green
    "aqua" -> Cyan
    "fuchsia" -> Magenta
    "darkgray" -> DarkGray
    _ -> ColorDefault
  match name
    "type" -> scheme(colorType=clr, colorTypeCon=clr, colorTypeKeyword=clr, colorEffect=clr)
    "kind" -> scheme(colorKind=clr)
    "marker" -> scheme(colorMarker=clr)
    "warning" -> scheme(colorWarning=clr)
    "error" -> scheme(colorError=clr)
    "source" -> scheme(colorSource=clr)
    "interpreter" -> scheme(colorInterpreter=clr)
    "command" -> scheme(colorCommand=clr)
    "keyword" -> scheme(colorKeyword=clr)
    "typecon" -> scheme(colorTypeCon=clr)
    "typevar" -> scheme(colorTypeVar=clr)
    "typekeyword" -> scheme(colorTypeKeyword=clr)
    "range" -> scheme(colorRange=clr)
    "sep" -> scheme(colorSep=clr)
    "comment" -> scheme(colorComment=clr)
    "reserved" -> scheme(colorReserved=clr)
    "reservedop" -> scheme(colorReservedOp=clr)
    "special" -> scheme(colorSpecial=clr)
    "string" -> scheme(colorString=clr)
    "number" -> scheme(colorNumber=clr)
    "module" -> scheme(colorModule=clr)
    "effect" -> scheme(colorEffect=clr)
    "parameter" -> scheme(colorParameter=clr)
    "cons" -> scheme(colorCons=clr)
    "constructor" -> scheme(colorCons=clr)
    "none" -> makeColorScheme(ColorDefault)
    "all" -> makeColorScheme(clr)
      
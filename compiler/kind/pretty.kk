import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/printer
import compiler/kind/kind
import compiler/common/name
import compiler/common/failure
import compiler/platform/config

alias prettyKindEff = <pure, compFlags>

fun kindColon(colors: colorScheme)
  ":".text.color(colors.colorSep)

fun keyword(s: string, colors: colorScheme)
  s.text.color(colors.colorKeyword)

// Generate nice quantifier names
fun niceKinds(kinds: list<kind>, colors: colorScheme): prettyKindEff list<doc>
  kinds.map(fn(k) k.ppKind(colors, precTop))

fun prettyKind(k: kind, cscheme: colorScheme): prettyKindEff doc
  k.ppKind(cscheme, precTop)

// Show
fun pretty(k: kind)
  k.ppKind(ColorScheme(), precTop)

// precedence
alias prec = int
val precTop = 0
val precQuant = 1
val precArrow = 2
val precApp = 3
val precAtom = 4

fun pparens(d: doc, contextPrec: prec, prec: prec)
  if contextPrec > prec then d.parens
  else d

fun commaParens(xs, f)
  xs.map(f).tupled

fun collectFunArgs(k: kind)
  match k
    KApp(KApp(KCon(name), k1), k2) | name == "->".newName ->
      Cons(k1, k2.unsafe-decreasing.collectFunArgs)
    _ -> [k]

fun ppKind(k: kind, cscheme: colorScheme, prec: prec)
  val nm = match k
    KCon(n) -> name/pretty(n)
    KApp(KApp(KCon(name), k1), k2) | name == "->".newName ->
      val x = match k2.collectFunArgs
        [res] -> 
          k1.ppKind(cscheme, precArrow) |+| 
          res.ppKind(cscheme, precArrow - 1)
        args -> 
          Cons(k1, args.init).commaParens(fn(k') k'.ppKind(cscheme, precTop)) |+| 
          "->".text |+| args.last.unjust.ppKind(cscheme, precArrow - 1)
      x.pparens(prec, precArrow)
    KApp ->
      val x = match k.collectFunArgs
        Cons(k', ks) -> 
          k'.ppKind(cscheme, precApp - 1) |.| 
          ks.commaParens(fn(x) x.ppKind(cscheme, precTop))
        _ -> fail("kind/pretty ppKind.KApp: match failure")
      x.pparens(prec, precApp)
  nm.color(cscheme.colorKind)

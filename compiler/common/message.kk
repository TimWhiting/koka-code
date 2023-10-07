import compiler/lib/pprint
import compiler/common/failure
import compiler/platform/config
import compiler/common/range
import compiler/common/color-scheme

// Pretty print helpers
fun ppRange(r: range, endToo: bool)
  r.showRange(endToo).text.color(colors.colorRange)

fun table(xs: list<(doc, doc)>)
  tablex(1, xs)

fun tablex(n: int, xs: list<(doc, doc)>)
  val headers = xs.map(fst)
  val headerwidth = headers.map(fn(x) x.show.count).maximum
  if headerwidth <= 0 then vcat(xs.map(snd)).indent(n)
  else vcat(xs.map(fn((hd, d)) hd.fill(headerwidth) |.| colon |+| align(d)))

// Source from range
fun sourceFromRanges(rngs: list<range>)
  rngs.map(sourceFromRange)

fun docsFromRanges(rngs: list<range>)
  rngs.map(fn(r) r.docFromRange)

fun docFromRange(r: range)
  fun removeIndent(ls: list<string>)
    val i = Cons(0, ls.map(fn(l) l.list.take-while(isSpace).length)).minimum
    ls.map(fn(l) l.list.drop(i).string)
  fun limitLineLen(line: string, n: int)
    if line.count <= n then line
    else
      val n3 = n / 3
      val (x, y) = line.list.split(2 * n3)
      val pre = x.reverse.drop-while(fn(c) !c.isSpace).reverse
      val post = y.reverse.take(n3).reverse.drop-while(fn(c) !c.isSpace)
      pre.string ++ " ... " ++ post.string
  fun limitLines(ls: list<string>, n: int)
    if ls.length <= n then ls.removeIndent
    elif n <= 2 then fail("common/message docFromRange.limitLines: illegal n")
    else
      val n2 = n / 2
      val pre = ls.take(n2)
      val post = ls.reverse.take(n2).reverse
      val prepost = (pre ++ post).removeIndent
      prepost.take(n2) ++ ["..."] ++ prepost.drop(n2)
  val x = r.sourceFromRange.lines.limitLines(3).map(fn(l) l.limitLineLen(80))
  match x
    Nil -> empty
    src -> src.map(text).vcat.align.color(colors.colorSource)

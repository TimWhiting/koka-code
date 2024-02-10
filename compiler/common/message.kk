import compiler/lib/pprint
import compiler/common/failure
import compiler/platform/config
import compiler/common/range
import compiler/common/color-scheme

// Pretty print helpers
fun pp-range(r: range, endToo: bool)
  r.showRange(endToo).text.color(colors.colorRange)

fun table(xs: list<(doc, doc)>)
  tablex(1, xs)

fun tablex(n: int, xs: list<(doc, doc)>)
  val headers = xs.map(fst)
  val headerwidth = headers.map(fn(x) x.show.count).maximum
  if headerwidth <= 0 then vcat(xs.map(snd)).indent(n)
  else vcat(xs.map(fn((hd, d)) hd.fill(headerwidth) |.| colon |+| align(d)))

// Source from range
fun source-from-ranges(rngs: list<range>)
  rngs.map(source)

fun docs-from-ranges(rngs: list<range>)
  rngs.map(fn(r) r.doc-from-range)

fun doc-from-range(r: range)
  fun remove-indent(ls: list<string>)
    val i = Cons(0, ls.map(fn(l) l.list.take-while(isSpace).length)).minimum
    ls.map(fn(l) l.list.drop(i).string)
  fun limit-line-len(line: string, n: int)
    if line.count <= n then line
    else
      val n3 = n / 3
      val (x, y) = line.list.split(2 * n3)
      val pre = x.reverse.drop-while(fn(c) !c.isSpace).reverse
      val post = y.reverse.take(n3).reverse.drop-while(fn(c) !c.isSpace)
      pre.string ++ " ... " ++ post.string
  fun limit-lines(ls: list<string>, n: int)
    if ls.length <= n then ls.remove-indent
    elif n <= 2 then fail("common/message docFromRange.limitLines: illegal n")
    else
      val n2 = n / 2
      val pre = ls.take(n2)
      val post = ls.reverse.take(n2).reverse
      val prepost = (pre ++ post).remove-indent
      prepost.take(n2) ++ ["..."] ++ prepost.drop(n2)
  val x = r.source-from-range.lines.limit-lines(3).map(fn(l) l.limit-line-len(80))
  match x
    Nil -> pprint/empty
    src -> src.map(text).vcat.align.color(colors.colorSource)

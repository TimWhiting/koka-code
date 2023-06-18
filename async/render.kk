import std/num/float64

type window;
value struct offset (dx : float64, dy: float64)

fun (==) (a: offset, b: offset) : bool
  a.dx == b.dx && a.dy == b.dy

fun (+) (a: offset, b: offset) : offset
  Offset(a.dx + b.dx, a.dy + b.dy)

fun (-) (a: offset, b: offset) : offset
  Offset(a.dx - b.dx, a.dy - b.dy)

value struct size (width : float64, height: float64)

fun (==) (a: size, b: size) : bool
  a.width == b.width && a.height == b.height

struct boxConstraints (minWidth : float64, maxWidth: float64, minHeight: float64, maxHeight: float64)

fun min(b: boxConstraints) : size
  Size(b.minWidth, b.minHeight)

fun max(b: boxConstraints) : size
  Size(b.maxWidth, b.maxHeight)

fun constrain(b: boxConstraints, s: size): size
  val width = if s.width < b.minWidth then b.minWidth else if s.width > b.maxWidth then b.maxWidth else s.width
  val height = if s.height < b.minHeight then b.minHeight else if s.height > b.maxHeight then b.maxHeight else s.height
  Size(width, height)

fun withConstraints(b: boxConstraints, minWidth: float64 = b.minWidth, maxWidth: float64 = b.maxWidth,
         minHeight: float64 = b.minHeight, maxHeight: float64 = b.maxHeight ): boxConstraints
  BoxConstraints(minWidth, maxWidth, minHeight, maxHeight)

fun trimHeight(b: boxConstraints, height: float64): boxConstraints
  val minHeight = if height > b.minHeight then 0.0 else b.minHeight - height
  val diffHeight = b.maxHeight - height
  val maxHeight = if diffHeight < minHeight then minHeight else diffHeight
  BoxConstraints(b.minWidth, b.maxWidth, minHeight, maxHeight)

fun (==) (a: boxConstraints, b: boxConstraints) : bool
  a.minWidth == b.minWidth && a.maxWidth == b.maxWidth && a.minHeight == b.minHeight && a.maxHeight == b.maxHeight



struct renderBox(offset: offset = Offset(0.0,0.0), size: size = Size(0.0,0.0), 
          parent:renderBox, constraints: boxConstraints = BoxConstraints(0.0,0.0,0.0,0.0))

value struct renderSingleChildBox(box : renderBox, child: renderBox)

value struct renderRoot(window: window, box: renderSingleChildBox)

fun render(window: window, box: renderSingleChildBox)
  window

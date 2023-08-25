import std/num/float64

value struct interval
  min: float64 = posinf
  max: float64 = neginf

fun contains(i: interval, x: float64): bool
  i.min <= x && x <= i.max

fun surrounds(i: interval, x: float64): bool
  i.min < x && x < i.max

fun clamp(i: interval, x: float64): float64
  if x < i.min then i.min
  else if x > i.max then i.max
  else x

val empty = Interval()
val universe = Interval(neginf, posinf)

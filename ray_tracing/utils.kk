import std/num/float64
import std/num/random

fun deg_to_rad(deg: float64): float64
  deg * pi / 180.0

fun random_double(): random float64
  random-float64()

fun random_double(min: float64, max: float64): random float64
  min + (max - min) * random_double()

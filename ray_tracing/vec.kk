import std/num/float64
import std/num/random
import utils

struct vec3
  x: float64 = 0.0
  y: float64 = 0.0
  z: float64 = 0.0

alias color = vec3
alias point = vec3

fun color(r: float64, g: float64, b: float64): color
  Vec3(r, g, b)

fun point(x: float64, y: float64, z: float64): point
  Vec3(x, y, z)

fun red(c: color): float64
  c.x

fun green(c: color): float64
  c.y

fun blue(c: color): float64
  c.z

fun (-)(v1: vec3, v2: vec3): vec3
  Vec3(v1.x - v2.x, v1.y - v2.y, v1.z - v2.z)

fun (+)(v1: vec3, v2: vec3): vec3
  Vec3(v1.x + v2.x, v1.y + v2.y, v1.z + v2.z)

fun dot(v1: vec3, v2: vec3): float64
  v1.x * v2.x + v1.y * v2.y + v1.z * v2.z

fun cross(v1: vec3, v2: vec3): vec3
  Vec3(v1.y * v2.z - v1.z * v2.y,
       v1.z * v2.x - v1.x * v2.z,
       v1.x * v2.y - v1.y * v2.x)

fun (*)(v: vec3, t: float64): vec3
  Vec3(v.x * t, v.y * t, v.z * t)

fun (/)(v: vec3, t: float64): vec3
  (1.0/t) * v

fun neg(v: vec3): vec3
  Vec3(0.0 - v.x, 0.0 - v.y, 0.0 - v.z)

fun random(): random vec3
  Vec3(random_double(), random_double(), random_double())

fun random(min: float64, max: float64): random vec3
  Vec3(random_double(min, max), random_double(min, max), random_double(min, max))

fun random_in_unit_sphere(): <div,random> vec3
  val p = random(-1.0, 1.0)
  if length2(p) < 1.0 then
    p
  else
    random_in_unit_sphere()

fun random_unit_vector(): <div,random> vec3
  unit(random_in_unit_sphere())

fun random_on_hemisphere(normal: vec3): <div,random> vec3
  val on_unit_sphere = random_unit_vector()
  if dot(on_unit_sphere, normal) > 0.0 then
    on_unit_sphere
  else
    on_unit_sphere.neg

inline fun(*)(t: float64, v: vec3): vec3
  v*t

fun unit(v: vec3): vec3
  v / length(v)

fun length2(v: vec3): float64
  v.x * v.x + v.y * v.y + v.z * v.z

fun length(v: vec3): float64
  sqrt(length2(v))

fun show(v: vec3): string
  show(v.x) ++ " " ++ show(v.y) ++ " " ++ show(v.z)

inline fun showPixel(f: float64): string
  int(255.99 * f).show

inline fun linear_to_gamma(f: float64): float64
  sqrt(f)

fun show_color(c: color, samples: int): string
  val scale = 1.0 / float64(samples)
  val c' = c * scale
  c'.x.linear_to_gamma.showPixel ++ " " ++ c'.y.linear_to_gamma.showPixel ++ " " ++ c'.z.linear_to_gamma.showPixel

fun [](v: vec3, i: int): float64
  if i == 0 then v.x elif i == 1 then v.y else v.z



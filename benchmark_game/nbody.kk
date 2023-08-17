import std/num/float64
import std/os/env

struct body
  x: float64
  y: float64
  z: float64
  vx: float64
  vy: float64
  vz: float64
  mass: float64

val days_per_year = 365.24
val solar_mass = 4.0*pi*pi

val jupiter = Body(
  4.84143144246472090e+00, 
  -1.16032004402742839e+00, 
  -1.03622044471123109e-01, 
  1.66007664274403694e-03 * days_per_year,
  7.69901118419740425e-03 * days_per_year,
  -6.90460016972063023e-05 * days_per_year, 
  9.54791938424326609e-04 * solar_mass
)
val saturn = Body(
  8.34336671824457987e+00, 
  4.12479856412430479e+00,
  -4.03523417114321381e-01,
  -2.76742510726862411e-03 * days_per_year,
  4.99852801234917238e-03 * days_per_year,
  2.30417297573763929e-05 * days_per_year,
  2.85885980666130812e-04 * solar_mass
)

val uranus = Body(
  1.28943695621391310e+01, 
  -1.51111514016986312e+01, 
  -2.23307578892655734e-01, 
  2.96460137564761618e-03 * days_per_year,
  2.37847173959480950e-03 * days_per_year,
  -2.96589568540237556e-05 * days_per_year,
  4.36624404335156298e-05 * solar_mass
)

val neptune = Body(
  1.53796971148509165e+01, 
  -2.59193146099879641e+01, 
  1.79258772950371181e-01, 
  2.68067772490389322e-03 * days_per_year,
  1.62824170038242295e-03 * days_per_year,
  -9.51592254519715870e-05 * days_per_year,
  5.15138902046611451e-05 * solar_mass
)

val sun = Body(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, solar_mass)

alias nbodysystem = list<body>

fun initSystem()
  val bodies = [sun, jupiter, saturn, uranus, neptune]
  val (px, py, pz) = bodies.foldl((0.0, 0.0, 0.0)) fn((accx, accy, accz), b)
    (accx + b.vx * b.mass, accy + b.vy * b.mass, accz + b.vz * b.mass)
  match bodies
    Cons(s, rst) -> Cons(s.offsetMomentum(px, py, pz), rst)
    x -> x

pub fun foldlmap(xs: list<a>, z: b, acc: ctx<list<a>>, f: (a, b) -> (a, b)): (list<a>, b)
  match xs
    Cons(x,xx) -> 
      val (x', res) = f(x, z)
      foldlmap(xx, res, (acc ++ ctx Cons(x', _)), f)
    Nil ->
      ((acc ++. Nil), z)

fun advanceV(bodies: nbodysystem, dt: float64)
  match bodies
    Cons(b1, rst) ->
      val (l, (dvx, dvy, dvz)) = rst.foldlmap((0.0, 0.0, 0.0), ctx _) fn(b2, (accx, accy, accz))
        val dx = b1.x - b2.x
        val dy = b1.y - b2.y
        val dz = b1.z - b2.z
        val d2 = dx * dx + dy * dy + dz * dz
        val mag = dt / (d2 * d2.sqrt)
        val b2' = b2(vx=b2.vx + dx*b1.mass * mag,vy=b2.vy + dy*b1.mass * mag, vz=b2.vz + dz*b1.mass * mag)
        val acc' = (accx + dx * b2.mass * mag, accy + dy * b2.mass * mag, accz + dz * b2.mass * mag)
        (b2', acc')
      Cons(b1(vx= b1.vx - dvx, vy= b1.vy - dvy, vz= b1.vz - dvz), l.advanceV(dt))
    Nil -> Nil

inline fun advance(bodies: nbodysystem, dt: float64)
  bodies.advanceV(dt).map(fn(b) b(x=b.x + dt*b.vx, y=b.y + dt*b.vy, z=b.z + dt*b.vz))

fun energy(bodies: nbodysystem)
  match bodies
    Cons(b1, rst) ->
      val e' = rst.foldl(0.0) fn(acce, b2)
        val dx = b1.x - b2.x
        val dy = b1.y - b2.y
        val dz = b1.z - b2.z
        acce + ((b1.mass * b2.mass) / (dx*dx + dy*dy + dz*dz).sqrt)
      0.5 * b1.mass * (b1.vx*b1.vx + b1.vy*b1.vy + b1.vz*b1.vz) - e' + rst.energy
    Nil -> 0.0

inline fun negate(f: float64)
  0.0 - f

inline fun offsetMomentum(b: body, px: float64, py: float64, pz: float64)
  b(vx= px.negate / solar_mass, vy= py.negate / solar_mass, vz= pz.negate / solar_mass)

fun main()
  val n = get-args()[0].default("1000").parse-int.unjust
  val bodies = initSystem()
  println(bodies.energy.show(9))
  val bds = list(0, n - 1).foldl(bodies) fn(bodies', _)
    bodies'.advance(0.01)
  println(bds.energy.show(9))

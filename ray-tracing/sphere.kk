import vec
import hittable
import ray
import std/num/float64
import interval

struct sphere
  center: point
  radius: float64
  mat: material

fun hit(s: sphere, r: ray, ray_t: interval): maybe<hitRecord>
  val oc = r.origin - s.center
  val a = r.dir.length2
  val half_b = oc.dot(r.dir)
  val c = oc.length2 - s.radius*s.radius
  val discriminant = half_b*half_b - a*c
  if discriminant < 0.0 then
    return Nothing
  
  val sqrtd = sqrt(discriminant)
  var root := (half_b.neg - sqrtd) / a
  if !ray_t.surrounds(root) then
    root := (half_b.neg + sqrtd) / a
    if !ray_t.surrounds(root) then
      return Nothing
  val p = r.at(root)
  val outward_normal = (p - s.center) / s.radius
  Just(HitRecord(root, p, outward_normal, s.mat).set_normal(r))
  

fun hittable(s: sphere): hittable
  fn(r, i) s.hit(r, i)
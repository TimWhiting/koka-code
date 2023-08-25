import vec
import ray
import interval
import std/num/random

type material
  Lambertian(albedo: color)
  Dielectric(index_of_refraction: float64)
  Metal(albedo: color, f: float64, fuzz: float64 = if f < 1.0 then f else 1.0)

rec type hitRecord
  HitRecord
    t: float64
    p: point
    normal: vec3
    mat: material
    front_face: bool = False

alias hittable = (r: ray, ray_t: interval) -> maybe<hitRecord>

fun set_normal(h: hitRecord, r: ray): hitRecord
  val ff = dot(r.dir, h.normal) < 0.0
  h(front_face=ff, normal=if ff then h.normal else h.normal.neg)

alias hitlist = list<hittable>

fun hit(l: hitlist, r: ray, ray_t: interval): maybe<hitRecord>
  l.foldl(Nothing) fn(acc: maybe<hitRecord>, h)
    match (h(r, Interval(ray_t.min, acc.map(fn(hr) hr.t).default(ray_t.max))), acc)
      (Just(hit_rec), Just(acc_rec)) -> if hit_rec.t < acc_rec.t then Just(hit_rec) else Just(acc_rec)
      (Just(hit_rec), Nothing) -> Just(hit_rec)
      _ -> acc
import vec
import ray
import interval

struct hitRecord
  t: float64
  p: point
  normal: vec3
  front_face: bool = False

alias hittable = (r: ray, ray_t: interval) -> maybe<hitRecord>

fun set_normal(h: hitRecord, r: ray): hitRecord
  val ff = dot(r.dir, h.normal) < 0.0
  h(front_face=ff, normal=if ff then h.normal else h.normal.neg)

alias hitlist = list<hittable>

fun hit(l: hitlist, r: ray, ray_t: interval): maybe<hitRecord>
  l.foldl(Nothing) fn(acc, h)
    match (h(r, ray_t), acc)
      (Just(hit_rec), Just(acc_rec)) -> if hit_rec.t < acc_rec.t then Just(hit_rec) else Just(acc_rec)
      (Just(hit_rec), Nothing) -> Just(hit_rec)
      _ -> acc
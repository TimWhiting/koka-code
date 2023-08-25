import vec

value struct ray
  origin: point
  dir: vec3

fun at(r: ray, t: float64): point
  r.origin + t * r.dir
import ray
import hittable
import interval
import vec
import std/num/float64
import std/num/random
import utils

struct camera
  aspect_ratio: float64
  image_width: int = 100
  samples_per_pixel: int = 100
  image_height: int = (image_width.float64 / aspect_ratio).int
  center: point = point(0.0,0.0,0.0)
  focal_length: float64 = 1.0
  viewport_height: float64 = 2.0
  viewport_width: float64 = viewport_height * (image_width.float64 / image_height.float64)
  viewport_u: vec3 = Vec3(viewport_width, 0.0, 0.0)
  viewport_v: vec3 = Vec3(0.0, 0.0-viewport_height, 0.0)
  pixel_delta_u: vec3 = viewport_u / image_width.float64
  pixel_delta_v: vec3 = viewport_v / image_height.float64
  viewport_upper_left: vec3 = center - Vec3(0.0, 0.0, focal_length) - (viewport_u / 2.0) - (viewport_v / 2.0)
  pixel00_loc: point = viewport_upper_left + 0.5 * (pixel_delta_u + pixel_delta_v)

fun render(cam: camera, world: hitlist)
  println("P3\n" ++ cam.image_width.show ++ " " ++ cam.image_height.show ++ "\n255")
  for(0, cam.image_height - 1) fn(j)
    trace("\nScanlines remaining: " ++ (cam.image_height - j).show ++ " ")
    for(0, cam.image_width - 1) fn(i)
      var c := color(0.0, 0.0, 0.0)
      for(0, cam.samples_per_pixel - 1) fn(_)
        val r = cam.get_ray(i, j)
        c := c + cam.ray_color(r, world)
      println(c.show_color(cam.samples_per_pixel))
  trace("Done.")

fun get_ray(c: camera, i: int, j: int): random ray
  val pixel_center = c.pixel00_loc + (c.pixel_delta_u * i.float64) + (c.pixel_delta_v * j.float64)
  val pixel_sample = pixel_center + c.pixel_sample_square()
  val ray_direction = pixel_sample - c.center
  Ray(c.center, ray_direction)

fun pixel_sample_square(c: camera)
  val px = -0.5 + random_double()
  val py = -0.5 + random_double()
  px * c.pixel_delta_u + py * c.pixel_delta_v

fun ray_color(c: camera, r: ray, world: hitlist, depth: int = 10): <div,random> color
  if depth < 0 then
    return color(0.0, 0.0, 0.0)
  match world.hit(r, Interval(0.001, posinf))
    Just(hit_rec) -> 
      val dir = hit_rec.normal + random_unit_vector()
      0.5 * c.ray_color(Ray(hit_rec.p, dir), world, depth - 1)
    Nothing -> 
      val unit_direction = r.dir.unit
      val a = 0.5 * (unit_direction.y + 1.0)
      ((1.0-a) * color(1.0, 1.0, 1.0)) + (a * color(0.5, 0.7, 1.0))

import vec
import sphere
import camera
import std/num/random

fun main()
  val sphere0 = Sphere(point(0.0, 0.0, -1.0), 0.6)
  val sphere1 = Sphere(point(0.0, -100.5, -1.0), 100.0)
  val world = [sphere0.hittable, sphere1.hittable]
  val cam = Camera(aspect_ratio = 16.0 / 9.0, image_width = 400, samples_per_pixel=100)
  cam.render(world)


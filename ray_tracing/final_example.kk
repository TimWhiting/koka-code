import vec
import sphere
import camera
import std/num/random
import material
import hittable

fun main()
  val material_ground = Lambertian(color(0.8, 0.8, 0.0))
  val material_center = Lambertian(color(0.1, 0.2, 0.5))
  val material_left = Dielectric(1.5)
  val material_right = Metal(color(0.8, 0.6, 0.2), 1.0)
  val sphere1 = Sphere(point(0.0, -100.5, -1.0), 100.0, material_ground)
  val sphere0 = Sphere(point(0.0, 0.0, -1.0), 0.5, material_center)
  val sphere2 = Sphere(point(-1.0, 0.0, -1.0), 0.5, material_left)
  val sphere2' = Sphere(point(-1.0, 0.0, -1.0), -0.4, material_left)
  val sphere3 = Sphere(point(1.0, 0.0, -1.0), 0.5, material_right)
  val world = [sphere0.hittable, sphere1.hittable, sphere2.hittable, sphere2'.hittable, sphere3.hittable]
  val cam = Camera(defocus_angle=10.0, focus_dist=3.4, aspect_ratio = 16.0 / 9.0, vfov=20.0, image_width = 400, samples_per_pixel=100, lookfrom=point(-2.0, 2.0, 1.0), lookat=point(0.0, 0.0, -1.0), vup=Vec3(0.0, 1.0, 0.0))
  cam.render(world)
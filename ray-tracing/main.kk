import vec
import sphere
import camera
import std/num/random
import material
import hittable
import utils
import std/num/float64

fun add(l, v)
  Cons(v, l)

fun main()
  var world := Nil
  val ground_mat = Lambertian(color(0.5, 0.5, 0.5))
  world := world.add(Sphere(point(0.0, -1000.0, 0.0), 1000.0, ground_mat).hittable)
  for(-11, 10) fn(a)
    for(-11, 10) fn(b)
      val choose_mat = random_double()
      val center = point(a.float64 + 0.9 * random_double(), 0.2, b.float64 + 0.9 * random_double())
      if (center - point(4.0, 0.2, 0.0)).length > 0.9 then
        if choose_mat < 0.8 then
          // diffuse
          val albedo = random() * random()
          val sphere_material = Lambertian(albedo)
          world := world.add(Sphere(center, 0.2, sphere_material).hittable)
        else if choose_mat < 0.95 then
          // metal
          val albedo = random(0.5, 1.0)
          val fuzz = random_double(0.0, 0.5)
          val sphere_material = Metal(albedo, fuzz)
          world := world.add(Sphere(center, 0.2, sphere_material).hittable)
        else
          // glass
          val sphere_material = Dielectric(1.5)
          world := world.add(Sphere(center, 0.2, sphere_material).hittable)
  val material1 = Dielectric(1.5)
  world := world.add(Sphere(point(0.0, 1.0, 0.0), 1.0, material1).hittable)

  val material2 = Lambertian(color(0.4, 0.2, 0.1))
  world := world.add(Sphere(point(-4.0, 1.0, 0.0), 1.0, material2).hittable)

  val material3 = Metal(color(0.7, 0.6, 0.5), 0.0)
  world := world.add(Sphere(point(4.0, 1.0, 0.0), 1.0, material3).hittable)

  val lookfrom = point(13.0, 2.0, 3.0)
  val lookat = point(0.0, 0.0, 0.0)
  val vup = Vec3(0.0, 1.0, 0.0)
  val aspect = 16.0 / 9.0
  val image_width = 1200
  val samples_per_pixel = 1
  val camera = Camera(samples_per_pixel=samples_per_pixel, image_width=image_width, aspect_ratio=aspect, lookat=lookat, lookfrom=lookfrom, vup=vup, vfov=20.0, defocus_angle=0.6, focus_dist=10.0)
  camera.render(world)
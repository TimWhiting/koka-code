import vec
import ray
import hittable
import std/num/random
import std/num/float64
import utils

fun scatter(mat: material, r_in: ray, hit: hitRecord): <div, random> maybe<(ray, color)>
  match mat
    Lambertian(albedo) -> 
      var scatter_dir := hit.normal + random_unit_vector()
      if scatter_dir.near_zero then
        scatter_dir := hit.normal
      val scattered = Ray(hit.p, scatter_dir)
      val attenuation = albedo
      Just((scattered, attenuation))
    Metal(albedo, _, fuzz) ->
      val reflected = reflect(r_in.dir.unit, hit.normal)
      val scattered = Ray(hit.p, reflected + (fuzz * random_unit_vector()))
      val attenuation = albedo
      if scattered.dir.dot(hit.normal) > 0.0 then
        return Just((scattered, attenuation))
      return Nothing
    Dielectric(ir) ->
      val attenuation = Vec3(1.0, 1.0, 1.0)
      val refract_ratio = if hit.front_face then (1.0 / ir) else ir
      val unit_dir = r_in.dir.unit
      val cos_theta = unit_dir.neg.dot(hit.normal).min(1.0)
      val sin_theta = sqrt(1.0 - cos_theta*cos_theta)
      val cannot_refract = (refract_ratio * sin_theta) > 1.0
      val direction = if cannot_refract || reflectance(cos_theta, refract_ratio) > random_double() then unit_dir.reflect(hit.normal) else unit_dir.refract(hit.normal, refract_ratio)
      val scattered = Ray(hit.p, direction)
      return Just((scattered, attenuation))

fun reflectance(cosine: float64, ref_idx: float64)
  val r0 = (1.0 - ref_idx) / (1.0 + ref_idx)
  val r02 = r0*r0
  r02 + (1.0 - r02)*pow(1.0 - cosine, 5.0)



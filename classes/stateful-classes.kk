module classes/stateful-classes

named effect animalSpeak
  fun speak(): ()
  fun animalInfo(): animalInfo // Base 
  fun animalInfoX(): animalInfoX // Extendable

struct animalInfo 
  name: string
  sound: string
  calls: int;

pub open type animalInfoX
  BaseAnimal
  DogInfo(breed: string)

fun animalDefault<a, h, e>(an: ref<h, animalInfo>, action: (ev<animalSpeak>) -> <console,read<h>,write<h>|e> a): <console,read<h>,write<h>|e> a
  with f <- named handler
    fun speak()
      val a = !an
      ("The " ++ a.name ++ " says " ++ a.sound ++ "! x" ++ a.calls.show).println()
      an := a(calls = a.calls + 1)
      ()
    fun animalInfo()
      !an
    fun animalInfoX()
      BaseAnimal
  action(f)

fun dog(action)
  val animal = AnimalInfo(name = "dog", sound = "woof", calls=0)
  var breed := "german shepard"
  val an = ref(animal)
  with super <- animalDefault(an)
  with f <- named handler
    fun speak()
      super.speak()
      val a = !an
      ("The " ++ breed ++ " " ++ a.name ++ " says " ++ a.sound ++ "! x" ++ a.calls.show).println()
      an := a(calls = a.calls + 1)
      ()
    fun animalInfo()
      !an
    fun animalInfoX()
      DogInfo(breed)
  action(f)

fun cat(action)
  animalDefault(ref(AnimalInfo(name = "cat", sound = "meow", calls=0)), action)

pub fun main()
  with d <- dog()
  with c <- cat()
  d.speak()
  c.speak()

  val l = Cons(d, Cons(c, Nil))
  l.foreach(fn (x) x.speak())
  l.foreach(fn (x) x.speak())
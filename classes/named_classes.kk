// Make the effects named
named linear effect animalSpeak
  fun speak(): ()

struct animalInfo 
  name: string
  sound: string

struct dogInfo
  breed: string

named effect val animal: animalInfo
named effect val dog-info: dogInfo

fun dog(action)
  with val animal = AnimalInfo(name = "dog", sound = "woof")
  with val dog-info = DogInfo(breed = "german shepard")
  with d <- named handler
    fun speak() ("The " ++ dog-info.breed ++ " " ++ animal.name ++ " says " ++ animal.sound ++ "!").println()
  action(d)

fun cat(action)
  with val animal = AnimalInfo(name = "cat", sound =  "meow")
  // Use a named handler that can then be passed around
  // I'm guessing essentially the vtable is passed around
  with c <- named handler
    fun speak() ("The " ++ animal.name ++ " says " ++ animal.sound ++ "!").println()
  action(c)
  

fun main()
  with d <- dog()
  with c <- cat()
  d.speak()
  c.speak()

  val l = Cons(d, Cons(c, Nil))
  l.foreach(fn (x) x.speak())
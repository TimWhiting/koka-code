// class interface as an effect
linear effect animalSpeak
  fun speak(): ()

// class data as structs
struct animalInfo 
  name: string
  sound: string

struct dogInfo
  breed: string

// access class data with an ambient effect value ** you don't have to pass it around yourself
effect val animal: animalInfo
effect val dog-info: dogInfo

// Aliases for more consise types
alias animalWithMethods = <animal, animalSpeak>
alias dogWithMethods = <animal, dog-info, animalSpeak>

val default = handler // This uses the animal data
  fun speak() ("The " ++ animal.name ++ " says " ++ animal.sound ++ "!").println()

val dogDefault = handler // This uses the dog-info and animal data
  fun speak() ("The " ++ dog-info.breed ++ " " ++ animal.name ++ " says " ++ animal.sound ++ "!").println()

// Creates a dog with data and with the dog method handler
fun dog(action: () -> <dogWithMethods,console|e> a): <console|e> a
  with val animal = AnimalInfo(name = "dog", sound = "woof")
  with val dog-info = DogInfo(breed = "german shepard")
  with dogDefault
  action()

// Creates a cat with animal data and with the default animal handler
fun cat(action: () -> <animalWithMethods,console|e> a): <console|e> a
  with val animal = AnimalInfo(name = "cat", sound =  "meow")
  with default
  action()

fun dog-speak(): <console> ()
  with dog
  speak()

fun cat-speak(): <console> ()
  with cat
  speak()

fun main()
  dog-speak()
  cat-speak()
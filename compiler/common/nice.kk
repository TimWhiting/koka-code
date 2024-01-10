import compiler/common/id
import compiler/type/type
import compiler/lib/pprint
import newstd/data/linearmap
import compiler/kind/kind

// Map identifiers to /nice/ strings.
alias nice = id-map<string>

val nice/empty = []

effect niceEff<k>
  fun extend-nice(tv: k): ()
  fun get-nice(tv: k): string 
  fun get-niceDoc(tv: k): doc 

fun niceEnv(f)
  var nice := nice/empty
  var effectIndex := -1
  var heapIndex := -1
  var typeIndex := -1
  var typeLetterIndex := -1
  var scopeIndex := -1
  with handler
    fun extend-nice(tv: typeVar)
      val x = 
        if tv.kind == kindEffect then
          effectIndex := effectIndex + 1
          "e" ++ (if effectIndex == 0 then "" else effectIndex.id/show)
        elif tv.kind == kindHeap then
          heapIndex := heapIndex + 1
          "h" ++ (if heapIndex == 0 then "" else heapIndex.id/show)
        elif tv.kind == kindScope then
          scopeIndex := scopeIndex + 1
          "s" ++ (if scopeIndex == 0 then "" else scopeIndex.id/show)
        else
          match typeLetterIndex
            4 -> 
              typeIndex := typeIndex + 1
              typeLetterIndex := 0
            _ ->
              typeLetterIndex := typeLetterIndex + 1
          (typeLetterIndex + 'a'.int).char.string ++ (if typeIndex == 0 then "" else typeIndex.id/show)
      nice := nice.extend(tv.tid, x)
      ()
    fun get-nice(tv: typeVar)
      nice.nice-show(tv.tid)
    fun get-niceDoc(tv: typeVar)
      nice.nice-pretty(tv.tid)
  f()

// Add fresh identifier substitutions give an (infinite) list of nice names.
fun extend(n: nice, id: int, name: string): nice
  n.set(id, name)

// Show the nice version of an identifier
fun nice-show(n: nice, id: id): string
  match n.maybe-get(id)
    Just(name) -> name
    Nothing -> id.id/show

// Pretty print an identifier nicely.
fun nice-pretty(n: nice, id: id): doc
  n.nice-show(id).text

/// Tests for identifiers
// fun main()
//   (idNil().newId.newIdFromId.idNumber == 1).show.println
//   (genId("test", 1).showId == "\"1\"").show.println
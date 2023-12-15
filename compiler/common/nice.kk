import compiler/common/id
import compiler/type/type
import compiler/lib/pprint
import newstd/data/linearmap
import compiler/kind/kind

// Map identifiers to /nice/ strings.
alias nice = id-map<string>

val niceEmpty = linearMap([])

effect niceEff<k>
  fun extendNice(tv: k): ()
  fun getNice(tv: k): string 
  fun getNiceDoc(tv: k): doc 

fun niceEnv(f)
  var nice := niceEmpty
  var effectIndex := -1
  var heapIndex := -1
  var typeIndex := -1
  var typeLetterIndex := -1
  var scopeIndex := -1
  with handler
    fun extendNice(tv: typeVar)
      val x = 
        if tv.kind == kindEffect then
          effectIndex := effectIndex + 1
          "e" ++ (if effectIndex == 0 then "" else effectIndex.show)
        elif tv.kind == kindHeap then
          heapIndex := heapIndex + 1
          "h" ++ (if heapIndex == 0 then "" else heapIndex.show)
        elif tv.kind == kindScope then
          scopeIndex := scopeIndex + 1
          "s" ++ (if scopeIndex == 0 then "" else scopeIndex.show)
        else
          match typeLetterIndex
            4 -> 
              typeIndex := typeIndex + 1
              typeLetterIndex := 0
            _ ->
              typeLetterIndex := typeLetterIndex + 1
          (typeLetterIndex + 'a'.int).char.string ++ (if typeIndex == 0 then "" else typeIndex.show)
      nice := nice.extend(tv.tid, x)
      ()
    fun getNice(tv: typeVar)
      nice.niceShow(tv.tid)
    fun getNiceDoc(tv: typeVar)
      nice.nicePretty(tv.tid)
  f()

// Add fresh identifier substitutions give an (infinite) list of nice names.
fun extend(n: nice, id: int, name: string): nice
  n.set(id, name)

// Show the nice version of an identifier
fun niceShow(n: nice, id: id): string
  match n.maybeGet(id)
    Just(name) -> name
    Nothing -> id.show

// Pretty print an identifier nicely.
fun nicePretty(n: nice, id: id): doc
  n.niceShow(id).text

/// Tests for identifiers
// fun main()
//   (idNil().newId.newIdFromId.idNumber == 1).show.println
//   (genId("test", 1).showId == "\"1\"").show.println
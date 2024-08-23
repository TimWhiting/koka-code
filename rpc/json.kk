import std/data/json
import std/num/random
import std/time/duration
pub import std/time/instant
import std/time/chrono
import std/time/time
import std/num/ddouble
import std/num/float64
import std/pretty/pprint
import parsers/alex/json-parse

struct person
  name: string
  age: int
  children: list<child>
  adult-children: list<person>

value struct child
  name: string

fun child/to-json(c: child)
  JSObj([("name", c.name.to-json)])

fun person/to-json(p: person)
  JSObj([("name", p.name.to-json), ("age", p.age.to-json), ("children", p.children.to-json), ("adult-children", p.adult-children.to-json)])

fun child/from-json(j: json, path: string): pure child
  match j
    JSObj(l) ->
      Child(
        l.from-json("name", path)
      )
    _ -> throw("Expecting child, got " ++ j.show, info=JsonDeserializationException(j, path))

fun person/from-json(j: json, path: string): pure person
  match j
    JSObj(l) ->
      Person(
        l.from-json("name", path),
        l.from-json("age", path),
        l.from-json("children", path),
        l.from-json("adult-children", path)
      )

fun person/show(j: person, indent: int=0)
  val ind = " ".repeat(indent + 2)
  "Person: " ++ j.name ++ " " ++ j.age.show ++ 
    "\n" ++ ind ++ j.children.show ++ 
    "\n" ++ ind ++ j.adult-children.map(fn(c) c.show(indent + 2)).join("\n" ++ ind)

fun child/show(c: child)
  c.name
 
fun test1()  
  val person = Person("Gpa", 55, [Child("A"), Child("B")], [Person("C", 28, [Child("D"), Child("E")], [])])
  person.to-json.pretty.show.println
  person.to-json.parse(person/from-json).show.println
  r#"{"name": "Gpa", "age": 58, "children": [], "adult-children": []}"#.json/parse.parse(person/from-json).show.println
  r#"{"name":"Gpa142749579","age":365380512,"children":[{"name":"another child219059342"}],"adult-children":[]}"#.json/parse.parse(person/from-json).show.println

  val o = JSObj([
      ("name", "Gpa".to-json), 
      ("age", 56.to-json), 
      ("children", JSList([])), 
      ("adult-children", JSList([Child("F").to-json]))])
  o.parse(person/from-json).show.println

fun generatePerson()
  Person(
    name= "Gpa" ++ random-int().show, 
    age=random-int(), 
    children=list(1,min(1,random-int()%4)).map(fn(c) Child("another child"++ random-int().show)), 
    adult-children=list(1,if random-int()%4 > 1 then random-int() % 4 else 0).map(fn(c) generatePerson())
  )

fun generatePeople(n: int)
  if n == 0 then Nil else Cons(generatePerson(), generatePeople(n - 1))

fun people/count(p: person)
  1 + p.adult-children.map(count).sum + p.children.length

fun main()
  val generated = generatePeople(10000)
  val tstart = now()
  val pjson = generated.map(to-json).map(show)
  val tend = now()
  // ("[" ++ pjson.join(",") ++ "]").println
  val persons = pjson.map(fn(p) p.parse.parse(person/from-json))
  val tend2 = now();
  val nump = persons.map(people/count).sum
  val toj = (tend - tstart).milli-seconds
  val fromj = (tend2 - tend).milli-seconds
  "total num people".println
  nump.println
  "total ms to-json".println
  toj.println
  "total ms from-json".println
  fromj.println
  (fromj.float64 / toj.float64).show(2).println
  "people/ms to-json".println
  (nump.float64 / toj.float64).show(2).println
  "people/ms from-json".println
  (nump.float64 / fromj.float64).show(2).println
  ()



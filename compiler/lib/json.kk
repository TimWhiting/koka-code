import newstd/text/parse
import std/data/linearmap
import std/text/regex
import std/num/float64

type jsValue
  JsNull
  JsBool(b: bool)
  JsInt(s: string, i:int)
  JsDouble(s: string, d:float64)
  JsString(s: string)
  JsArray(l: list<jsValue>)
  JsObject(o: jsObject<jsValue>)

alias jsObject<a> = linearMap<string, a>

fun toString(v: jsValue)
  match v
    JsString(s) -> s
    _ -> v.show

fun show(v: jsValue)
  match v
    JsNull -> "null"
    JsBool(b) -> if b then "true" else "false"
    JsInt(i) -> i.show
    JsDouble(d) -> d.show
    JsString(s) -> s.show
    JsArray(l) -> "[" ++ l.map(show).join(", ") ++ "]"
    JsObject(o) -> "{" ++ o.list.map(fn ((k, v1)) k ++ ": " ++ v1.show).join(",\n ") ++ "}"

fun jsLookup(v: jsValue, keys: list<string>): jsValue
  match keys
    Nil -> v
    Cons(k, ks) ->
      match v
        JsObject(o) -> 
          match o.lookup(k)
            Just(v1) -> jsLookup(v1, ks)
            Nothing -> JsNull
        JsArray(vs) -> 
          match k.parse-int
            Just(i) -> 
              match vs[i]
                Just(v1) -> jsLookup(v1, ks)
                Nothing -> JsNull
            Nothing -> JsNull
        _ -> JsNull

fun jsFind(v: jsValue, def: jsValue, keys: list<string>): jsValue
  match v.jsLookup(keys)
    JsNull -> def
    v1 -> v1

val hexLeadRegex = r"0[xX]".regex();
fun hexadecimal()
  takePattern(leadingRegex).string ++ takePattern(hexLeadRegex).string ++ takePattern(integerRegex).string

val leadingHexDotRegex = r"^.[0-9a-fA-F_]+([eEpP][+-]?[0-9a-fA-F_]+)?".regex() 
val wholeHexFloatRegex = r"^[0-9a-fA-F_]+(\.[0-9a-fA-F_]+)?([eEpP][+-]?[0-9a-fA-F_]+)?".regex() 
val integerRegex = r"^[0-9a-fA-F_]+".regex() 
fun integer()
  takePattern(leadingRegex).string ++ takePattern(integerRegex).string

val leadingRegex = r"[+-]".regex()
fun exp()
  takePattern(leadingRegex).string ++ integer()
  
fun decfloat()
  takePattern(leadingRegex).string ++ (fn() takePattern(wholeHexFloatRegex).string).or({takePattern(leadingHexDotRegex).string})

fun hexfloat()
  takePattern(leadingRegex).string++ hexadecimal() ++ (fn() takePattern(wholeHexFloatRegex).string).or({takePattern(leadingHexDotRegex).string})

fun pLit()
  with scope("plit")
  ors([{text("true"); JsBool(True)},{text("false"); JsBool(False)},{text("null"); JsNull}])

fun pFloat()
  with atomic
  val d = or({decfloat().split("_").join}, {hexfloat().split("_").join})
  JsDouble(d, d.parse-float64.unjust)

fun pInteger()
  with atomic
  val d = integer().split("_").join
  JsInt(d, d.parse-int.unjust)

val stringRegex = "^\"[^\\\\\"]*(?:\\\\.[^\"\\\\]*)*\"".regex()

inline fun takeString(): parse<string> sslice
  takePattern(stringRegex)

fun pString()
  with scope("pstring")
  val s = takeString()
  JsString(s.subslice(1, s.count - 1).string)

fun pArray()
  with scope("parray")
  pToken("[")
  val xs = separatedTrailing(pValue,{pToken(",")})
  optional(pWhitespace)
  pToken("]")
  JsArray(xs)

fun pMember(): <pure,parse<string>> (string, jsValue)
  with scope("pmember")
  val k = takeString()
  optional(pWhitespace)
  pToken(":")
  val v = pValue()
  (k.string, v)

fun pObject()
  with scope("pobject")
  pToken("{")
  val members = separatedTrailing(pMember, {pToken(",")})
  optional(pWhitespace)
  val o = JsObject(LinearMap(members))
  pToken("}")
  o

fun pValue(): <pure,parse<string>> jsValue
  with scope("pvalue")
  val v = ors([pArray,pObject,pLit,pFloat,pInteger,pString])
  optional(pWhitespace)
  v

val spacesRegex = r"^([ \n\t\r]|\/\/[^\n]+)+".regex()
fun pWhitespace()
  spacesRegex.takePattern()

fun pToken(s: string)
  text(s)
  optional(pWhitespace)

fun parse(s: string): ()
  s.println
  val x = match pValue.run(s)
    Right(e) -> e.show
    Left(err) -> "Error:\n" ++ err.show()
  x.println
  
fun parse2(p, s: string, rshow)
  s.println
  val x = match p.run(s)
    Right(e) -> e.rshow
    Left(err) -> "Error:\n" ++ err.show()
  x.println
  
fun main()
  parse(r#"{
  "hello":"world", // Something here
}"#
  )
  
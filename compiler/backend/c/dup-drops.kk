import compiler/core/core
import compiler/lib/pprint
import compiler/type/type
import compiler/common/name
import compiler/backend/c/helpers
import compiler/common/failure
import compiler/platform/config
import compiler/common/syntax
import newstd/data/sort

fun genBoxUnbox(nm: name, info: dataInfo, drepr: dataRepr)
  val tname = nm.typeClassName
  tname.genBox(info, drepr)
  tname.genUnbox(info, drepr)

fun genBoxCall(tp: ktype, arg: doc)
  val prim = "box"
  match tp.cType
    CFun -> primNameType(prim, "function_t") |.| tupled([arg, contextDoc])
    CPrim(v) | v == "kk_unit_t" || v == "bool" || v == "kk_string_t" -> primNameType(prim, v) |.| parens(arg)
    CData(nm) -> primName(prim, nm.cppName) |.| tupled([arg, contextDoc])
    _ -> primNameType(prim, tp.cppType.show) |.| tupled([arg, contextDoc])

fun genUnboxCallOwned(tp: ktype, arg: doc)
  genUnboxCall(tp, arg, "KK_OWNED".text)

fun genUnboxCallBorrowed(tp: ktype, arg: doc)
  genUnboxCall(tp, arg, "KK_BORROWED".text)

fun genUnboxCall(tp: ktype, arg: doc, argBorrow: doc)
  val prim = "unbox"
  match tp.cType
    CFun -> primNameType(prim, "function_t") |.| tupled([arg, contextDoc]) // no borrow
    CPrim(v) | v == "kk_unit_t" || v == "bool" || v == "kk_string_t" -> primNameType(prim, v) |.| arg.parens // no borrow, no context
    CPrim(v) -> primNameType(prim, v) |.| tupled(if v.cPrimCanBeBoxed then [arg, argBorrow, contextDoc] else [arg, contextDoc])
    CData(nm) -> primName(prim, nm.cppName) |.| tupled([arg, argBorrow, contextDoc])
    CBox -> primNameType(prim, tp.cppType.show) |.| tupled([arg, contextDoc])

fun dataStructAsMaybeSplit(l: list<conInfo>)
  match l
    Cons(ci1, Cons(ci2, Nil)) -> if ci1.params.is-nil then (ci1, ci2) else (ci2, ci1)
    _ -> fail("backend/c/from-core dataStructAsMaybeSplit: expected two constructors for a maybe like type, got: " ++ l.show-list(show))

fun genBox(nm: name, info: dataInfo, drepr: dataRepr)
  val initDoc = "static inline kk_box_t".text |.| nm.cppName |.| "_box".text |.| parameters([nm.cppName |+| "_x".text])
  val restDoc = match drepr
    DataEnum -> "return".text |+| "kk_enum_box".text |.| tupled(["_x".text]) |.| semi
    DataIso ->
      val conInfo = info.constrs.head.unjust
      val (isoName, isoTp) = conInfo.params.head.unjust
      "return".text |+| genBoxCall(isoTp, "_x.".text |.| isoName.unqualify.cppName) |.| semi
    DataStructAsMaybe ->
      val (conNothing, conJust) = info.constrs.dataStructAsMaybeSplit
      val (conJustFieldName, conJustFieldTp) = conJust.params.head.unjust
      val boxField = genBoxCall(conJustFieldTp, "_x._cons.".text) |.| conJust.name.ppDefName |.| ".".text |.| conJustFieldName.unqualify.cppName
      "if".text |+| parens(conNothing.conTestName |.| arguments(["_x".text])) |+| "{ return kk_box_Nothing(); }".text |-|
      "  else".text |+| "{ return kk_box_Just".text |.| arguments([boxField]) |.| semi |+| "}".text
    _ ->
      match info.def
        DataDefValue(ValueRepr(_, scancount, _)) ->
          val docScanCount = scancount.pretty |+| "/* scan count */".text
          vcat(["kk_box_t _box;".text, "kk_valuetype_box".text |.| arguments([nm.cppName, "_box".text, "_x".text, docScanCount]) |.| semi, "return _box;".text])
        _ -> "return".text |+| (if drepr.dataReprMayHaveSingletons then "kk_datatype_box" else "kk_datatype_ptr_box").text |.| tupled(["_x".text]) |.| semi
  emitToH(initDoc |+| block(restDoc))

fun genUnbox(nm: name, info: dataInfo, drepr: dataRepr)
  val initDoc = "static inline".text |+| nm.cppName |+| nm.cppName |.| "_unbox".text |.| parameters(["kk_box_t _x".text, "kk_borrow_t _borrow".text])
  val restDoc = match drepr
    DataEnum -> "return".text |+| nm.cppName.parens |.| "kk_enum_unbox".text |.| tupled(["_x".text])
    DataIso ->
      val conInfo = info.constrs.head.unjust
      val isoTp = conInfo.params.head.unjust.snd
      "return".text |+| conInfo.conCreateName |.| arguments([genUnboxCall(isoTp, "_x".text, "_borrow".text)])
    DataStructAsMaybe ->
      val (conNothing, conJust) = info.constrs.sortBy(fn(ci1, ci2) ci1.params.length.compare(ci2.params.length)).dataStructAsMaybeSplit
      val (_, conJustFieldTp) = conJust.params.head.unjust
      "if (kk_box_is_Nothing(_x))".text |+| "{ return".text |+| conNothing.conCreateName |.| arguments([]) |.| semi |+| "}".text
      |-| "  else".text |+| (
        "{ return".text |+| conJust.conCreateName |.| arguments([
            genUnboxCall(conJustFieldTp, "kk_unbox_Just".text |.| arguments(["_x".text, "_borrow".text]), "_borrow".text)])
          |.| semi |+| "}".text
      )
    _ | drepr.isValue -> [nm.cppName |+| "_unbox;".text, "kk_valuetype_unbox".text |.| arguments([nm.cppName, "_unbox".text, "_x".text, "_borrow".text]) |.| semi, "return _unbox".text].vcat
    _ -> "return".text |+| (if drepr.dataReprMayHaveSingletons then "kk_datatype_unbox" else "kk_datatype_ptr_unbox").text |.| tupled(["_x".text])
  emitToH(initDoc |+| block(restDoc) |.| semi)

// con infos are sorted with singletons first
fun genDupDrop(nm: name, info: dataInfo, drepr: dataRepr, conInfos: list<(conInfo, conRepr, list<(name, ktype)>, int)>)
  genDupDropX(True, nm, info, drepr, conInfos)
  genDupDropX(False, nm, info, drepr, conInfos)

fun genDupDropX(isDup: bool, nm: name, info: dataInfo, drepr: dataRepr, conInfos: list<(conInfo, conRepr, list<(name, ktype)>, int)>)
  val ret = if isDup then ["return _x".text] else []
  val dupDropTests =
    if drepr.is-dataEnum then ret
    elif conInfos.all(fn((_, cr, _, _)) cr.is-conSingleton) then ret
    elif drepr.is-dataIso then [genDupDropIso(isDup, conInfos.head.unjust)] ++ ret
    elif drepr.isDataStructOrLess then
      conInfos.map(fn(d) genDupDropTests(isDup, drepr, d)).genDupDropMatch ++ ret
    else
      if isDup then ["return".text |+| (
        if drepr.dataReprMayHaveSingletons then "kk_datatype_dup".text |.| arguments(["_x".text]) 
        else "kk_datatype_ptr_dup".text |.| arguments(["_x".text])) |.| semi]
      else [
        (if drepr.dataReprMayHaveSingletons then "kk_datatype_drop" else "kk_datatype_ptr_drop").text |.| 
        arguments(["_x".text]) |.| semi]
  emitToH("static inline".text |+| 
    (if isDup then nm.cppName |+| nm.cppName |.| "_dup".text else "void".text |+| nm.cppName |.| "_drop".text) |.| 
    parameters([nm.cppName |+| "_x".text]) |+| block(vcat(dupDropTests)))

fun genDupDropIso(isDup: bool, (_, _, tnames, _): (conInfo, conRepr, list<(name, ktype)>, int))
  match tnames
    [(name, tp)] -> genDupDropCall(isDup, tp, "_x.".text |.| name.cppName).map(fn(x) x |.| semi).hcat
    _ -> fail("backend/c/genDupDropIso: invalid arguments")

// coninfos are sorted with singletons first
fun genDupDropMaybe(isDup: bool, l: list<(conInfo, conRepr, list<(name, ktype)>, int)>)
  match l
    [(conNothing, _, _, _), (conJust, _, [(fname, ftp)], _)] ->
      "if".text |+| parens("!".text |.| conNothing.conTestName |.| arguments(["_x".text])) |+|
      block(vcat(genDupDropCall(isDup, ftp, "_x._cons.".text |.| conJust.name.ppDefName |.| dot |.| fname.cppName)) |.| semi)

fun genDupDropMatch(branches0: list<(doc, list<doc>)>)
  val branches = branches0.filter(fn(b) b.snd.is-cons)
  val complete = branches.length == branches0.length
  fun genBranch(iff0, (test, stats))
    iff0.text |+| test.parens |+| block1(stats)
  match branches
    [] -> []
    [(_, stats)] | stats.is-nil || complete -> stats
    Cons(b, bs) -> 
      [genBranch("if", b)] ++ 
      (if complete then bs.init else bs).map(fn(b') genBranch("else if", b')) ++
      (if complete then ["else".text |+| block1(bs.last.unjust.snd)] else [])

fun genDupDropTests(isDup: bool, drepr: dataRepr, (ci, _, cfields, _): (conInfo, conRepr, list<(name, ktype)>, int))
  val dupdropfields = genDupDropFields(isDup, drepr, ci, cfields)
  (ci.conTestName |.| arguments(["_x".text]), dupdropfields)

fun genDupDropTestsX(isDup: bool, drepr: dataRepr, lastIdx: int, ((ci, _, cfields, _), idx): ((conInfo, conRepr, list<(name, ktype)>, int), int))
  val stats = genDupDropFields(isDup, drepr, ci, cfields)
  if lastIdx == idx then 
    if stats.is-nil then empty elif lastIdx == 1 then stats.vcat else "else".text |+| stats.vcat.block
  else
    val t = if idx == 1 then "if".text else "else if".text
    t |+| parens(ci.conTestName |.| arguments(["_x".text])) |+| (if stats.is-nil then "{ }".text else stats.vcat.block)

fun genDupDropFields(isDup: bool, drepr: dataRepr, ci: conInfo, cfields: list<(name,ktype)>)
  cfields.map(fn((nm, tp)) genDupDropCall(isDup, tp, if drepr.needsTagField then "_x._cons.".text |.| ci.name.ppDefName else "_x".text |.| dot |.| nm.cppName)).concat.map(fn(d) d |.| semi)

fun genDupDropCallX(prim: string, tp: ktype, args: doc)
  match tp.cType
    CFun -> [primNameType(prim, "function_t") |.| args]
    CBox -> [primNameType(prim, "box_t") |.| args]
    CPrim(v) | v == "kk_integer_t" || v == "kk_string_t" || v == "kk_vector_t" || v == "kk_evv_t" || v == "kk_ref_t" || v == "kk_reuse_t" || v == "kk_box_t"
      -> [primNameType(prim, v) |.| args]
    CPrim -> [text("kk_skip_" ++ prim) |.| args] // [] // text "value" |.| args
    CData(nm) -> [primName(prim, nm.cppName) |.| args]

fun genDupCall(tp: ktype, arg: doc)
  genDupDropCall(True, tp, arg).hcat

fun genDropCall(tp: ktype, arg: doc)
  genDupDropCall(False, tp, arg).hcat

fun genDupDropCall(isDup: bool, tp: ktype, arg: doc)
  if isDup then genDupDropCallX("dup", tp, arguments([arg]))
  else genDupDropCallX("drop", tp, arguments([arg]))

// The following functions are generated during "drop specialization" and "reuse specialization", 
// and only generated for heap allocated constructors so we can always use the `datatype_ptr` calls at runtime.
fun genIsUniqueCall(tp: ktype, arg: doc)
  ["kk_likely".text |.| parens("kk_datatype_ptr_is_unique".text |.| arguments([arg]))]

fun genFreeCall(tp: ktype, arg: doc)
  ["kk_datatype_ptr_free".text |.| arguments([arg])]

fun genDecRefCall(tp: ktype, arg: doc)
  ["kk_datatype_ptr_decref".text |.| arguments([arg])]

fun genDropReuseCall(tp: ktype, arg: list<doc>)
  ["kk_datatype_ptr_dropn_reuse".text |.| arguments(arg)]

fun genReuseCall(tp: ktype, arg: doc)
  ["kk_datatype_ptr_reuse".text |.| arguments([arg])]

fun genDropNCall(tp: ktype, args: list<doc>)
  ["kk_datatype_ptr_dropn".text |.| arguments(args)]

fun genHoleCall(tp: ktype)
  match tp.cType
    CPrim("kk_integer_t") -> "kk_integer_zero".text
    CPrim("kk_string_t") -> "kk_string_empty()".text
    CPrim("kk_vector_t") -> "kk_vector_empty()".text
    _ -> "kk_datatype_null()".text

import compiler/core/core
import compiler/common/name
import compiler/common/syntax
import compiler/lib/pprint
import compiler/type/type
import compiler/backend/c/helpers
import compiler/backend/c/dup-drops
import compiler/common/failure
import compiler/platform/config
import newstd/data/sort

// Generate value constructors for each defined type

fun genTypeDefs(tds: typeDefGroups): asmEff ()
  tds.map(genTypeDefGroup)
  ()

fun genTypeDefGroup(tds: typeDefGroup): asmEff ()
  tds.map(genTypeDefPre)
  tds.map(genTypeDefPost)
  ()

fun genTypeDefPre(td: typeDef)
  match td
    Synonym -> ()
    Data(info, isExtend) ->
      // generate the type constructor
      emitToH(linebreak |.| text("// " ++ (if info.isValue then "value type" else "type")) |+| info.name.pretty)
      val (dataRepr, conReprs) = info.dataRepr(isValue)
      if dataRepr.is-dataEnum then
        val enumIntTp = match info.def
          DataDefValue(ValueRepr(n, 0, _)) ->
            if n <= 1 then "uint8_t" elif n <= 2 then "uint16_t" elif n <= 4 then "uint32_t" else "uint64_t"
          _ -> "kk_intb_t" // should not happen!
        fun ppEnumCon((c: conInfo, _)) c.name.cppName
        emitToH(info.vis.cppVis |.| "enum".text |+| info.name.typeClassName.cppName |.| "_e".text |+|
          block(if conReprs.is-nil then info.name.cppName |.| "_empty".text else vcat(info.constrs.zip(conReprs).map(ppEnumCon).punctuate(comma))) |.| semi |-|
          "typedef".text |+| enumIntTp.text |+| info.name.typeClassName.cppName |.| semi |.| linebreak
          )
      elif dataRepr.isValue || isExtend then ()
      else
        emitToH(info.vis.cppVis |.| "struct".text |+| info.name.typeClassName.cppName |.| "_s".text |+| 
          block(vcat(["kk_block_t _block;".text] ++ (if dataRepr.is-dataOpen then ["kk_string_t _tag;".text] else []))) |.| semi |-|
          (if dataRepr.dataReprMayHaveSingletons then "typedef kk_datatype_t".text |+| info.name.typeClassName.cppName |.| semi 
           else "typedef kk_datatype_ptr_t".text |+| info.name.typeClassName.cppName |.| semi)
          )

fun genTypeDefPost(td: typeDef)
  match td
    Synonym -> ()
    Data(info, isExtend) ->
      // Generate the type constructor
      val (dataRepr, conReprs) = info.dataRepr(isValue)
      val noCons = conReprs.is-nil
      val nm = info.name

      // order fields of constructors to have their scan fields first
      val conInfoReprs = zip(info.constrs, conReprs)
      val conInfos = conInfoReprs.map fn((ci, crepr))
        val fields = ci.orderedParams
        val scanCount = ci.valueRepr.scanCount
        (ci, crepr, fields, scanCount)
      val maxSC = conInfos.maxScanCountOf
      val minSC = conInfos.minScanCountOf

      // generate types for constructors
      if dataRepr.is-dataEnum then ()
      else 
        conInfos.map(fn(ci) ci.genConstructorType(info, dataRepr))
        ()

      // wrap up the type definition
      if dataRepr.is-dataOpen && !isExtend then
        ()
      elif dataRepr.is-dataEnum || !dataRepr.isValue then
        ()
      else
        fun ppStructConField(c: conInfo)
          "struct".text |+| c.name.cppName |+| c.name.unqualify.cppName |.| semi
        if dataRepr.needsTagField then
          emitToH(
            info.vis.cppVis |.| "struct".text |+| nm.cppName |.| "_s".text |+|
            block("kk_value_tag_t _tag;".text |-| "union".text |+| 
              block(vcat(
                (info.constrs.map(ppStructConField) ++ 
                 (if maxSC > 1 && minSC != maxSC then ["kk_box_t _fields[".text |.| (maxSC - 1).pretty |.| "]".text] else []))
                )) |+| "_cons;".text) |.| semi
            |-| info.vis.cppVis |.| "typedef struct".text |+| nm.cppName |.| "_s".text |+| nm.typeClassName.cppName |.| semi
          )
        else
          emitToH(info.vis.cppVis |.| "typedef struct".text |+| (
            match (dataRepr, info.constrs)
              (DataIso, [c]) -> c.name.cppName
              (DataSingleStruct, [c]) -> c.name.cppName
              _ -> nm.cppName |.| "_s".text
            )
            |+| nm.typeClassName.cppName |.| semi
          )
      
      // generate functions for constructors
      val sconInfos = conInfos.sortBy(fn(ci1, ci2) ci1.fst.params.length.compare(ci2.fst.params.length)) // singletons first
      sconInfos.map(fn(ci) ci.genConstructor(info, dataRepr, maxSC))
      sconInfos.map(fn(ci) ci.genConstructorTest(info, dataRepr))

      // generate functions for the data type
      if !isExtend then
        nm.typeClassName.genDupDrop(info, dataRepr, sconInfos)
        nm.genBoxUnbox(info, dataRepr)
      else
        ()

fun genConstructorType((ci, crepr, cfields, _): (conInfo, conRepr, list<(name, ktype)>, int), info: dataInfo, drepr: dataRepr)
  match crepr
    ConEnum -> () // already in enum declaration
    ConSingleton | !drepr.isValue -> ()
    _ ->
      val typeField = if drepr.isValue then [] else ["struct".text |+| info.name.typeClassName.cppName |.| "_s".text |+| "_base;".text]
      val fields = typeField ++ cfields.map(ppConField)
      emitToH(ci.vis.cppVis |.| "struct".text |+| ci.name.cppName |+| 
        block(if fields.is-nil then "kk_box_t _unused;".text else fields.vcat) // avoid empty struct
        |.| semi)

fun ppConField((nm, tp): (name, ktype))
  tp.cppType |+| nm.unqualify.cppName |.| semi

fun genConstructor((ci, crepr, cfields, scanCount): (conInfo, conRepr, list<(name, ktype)>, int), info: dataInfo, drepr: dataRepr, maxScanCount: int)
  genConstructorBaseCast(ci, crepr, info, drepr)
  genConstructorCreate(ci, crepr, cfields, scanCount, maxScanCount, info, drepr)
  genConstructorAccess(ci, crepr, info, drepr)

fun genConstructorTest((ci, crepr, _, _): (conInfo, conRepr, list<(name, ktype)>, int), info: dataInfo, drepr: dataRepr)
  val nameDoc = ci.name.cppName
  val dataTypeTagDoc = "kk_datatype_tag".text |.| arguments(["x".text])
  val ctag = ppConTag(ci, crepr, drepr)
  val valueTagEq = "kk_value_tag_eq(x._tag,".text |+| ctag |.| ")".text

  emitToH(
    "static inline bool".text |+| ci.conTestName |.| parameters([info.name.typeClassName.cppName |+| "x".text])
    |+| block(
      match crepr
        ConEnum -> "x ==".text |+| ctag
        ConIso -> "true".text
        ConSingleton | drepr.isValue -> valueTagEq
        ConSingleton -> "kk_datatype_has_singleton_tag".text |.| ["x".text, ctag].tupled
        ConSingle -> "true".text
        ConStruct -> valueTagEq
        ConAsJust(asNothing=non) -> "!".text |.| conTestNameX(non) |.| arguments(["x".text])
        ConAsCons(asNil=non) -> // TODO kk_datatype_is_ptr may be faster on arm64?
          "!".text |.| non.conTestNameX |.| arguments(["x".text])
        ConNormal ->
          text(if drepr.dataReprMayHaveSingletons then "kk_datatype_has_ptr_tag" else "kk_datatype_ptr_has_tag") |.| arguments(["x".text, ctag])
        ConOpen ->
          "kk_string_ptr_eq_borrow".text |.| tupled([
            parens("kk_datatype_as".text |.| arguments([
              "struct".text |+| info.name.typeClassName.cppName |.| "_s*".text
            ])) |.| "->_tag".text
            ,ctag
          ])
    ) |.|
    ");".text
  )

fun ppConTag(ci: conInfo, crepr: conRepr, drepr: dataRepr)
  match crepr 
    ConOpen -> "tag".makeHiddenName(ci.name).cppName
    ConEnum -> ci.name.cppName
    ConSingleton | drepr.is-dataAsMaybe -> "KK_TAG_NOTHING".text
    ConAsJust -> "KK_TAG_JUST".text
    _ | drepr.needsTagField -> "kk_value_tag(".text |.| crepr.tag.pretty |.| ")".text
    _ -> "(kk_tag_t)".text |.| crepr.tag.pretty.parens


fun genConstructorCreate(ci: conInfo, crepr: conRepr, allFields: list<(name, ktype)>, scanCount: int, maxScanCount: int, info: dataInfo, drepr: dataRepr)
  if drepr.is-dataOpen then
    emitToH("extern kk_string_t".text |+| ci.conTagName |.| semi)
  val at = "at".newHiddenName
  val cpath = "cpath".newHiddenName
  val hasCPath = crepr.hasCtxPath && allFields.is-cons
  val nameDoc = ci.name.cppName
  val ctag = ppConTag(ci, crepr, drepr)
  val (paddingFields, conFields) = allFields.partition(fn(f) f.fst.isPaddingName)
  emitToH("static inline".text |+| info.name.typeClassName.cppName |+| ci.conCreateName |.| 
   ntParameters(
    (if drepr.isValue || conFields.is-nil || drepr.is-dataAsMaybe then [] else [(at, typeReuse)])
    ++ (if hasCPath then [(cpath, typeInt32)] else []) ++ ci.params
    ) |+|
    block(
      match crepr
        ConEnum -> "return ".text |+| ctag |.| semi
        ConSingleton | !drepr.isValue -> "return kk_datatype_from_tag".text |.| ctag.parens |.| semi
        ConIso -> 
          val tmp = "_con".text
          vcat([
            info.name.typeClassName.cppName |+| tmp |+| "= {".text |+| conFields.head.unjust.fst.ppDefName |+| "};".text, 
            "return".text |+| tmp |.| semi])
        _ ->
          val tmp = "_con".text
          fun assignField((name, _), f)
            f(name.ppDefName) |+| "=".text |+| name.ppDefName |.| semi
          if drepr.isValue then
            vcat((
              if drepr.needsTagField then
               [info.name.typeClassName.cppName |+| tmp |.| semi,
                tmp |.| "._tag =".text |+| ctag |.| semi] ++
                conFields.map(fn(cf) cf.assignField(fn(fld) tmp |.| "._cons.".text |.| ci.name.ppDefName |.| ".".text |.| fld))
                ++ paddingFields.map(fn((padding, _)) tmp |.| "._cons.".text |.| ci.name.ppDefName |.| ".".text |.| padding.ppDefName |+| "= kk_box_null();".text)
                ++ list(scanCount - 1, maxScanCount - 2).map(fn(i) tmp |.| "._cons._fields[".text |.| i.pretty |.| "] = kk_box_null();".text)
              else []
              ) ++
              ["return".text |+| tmp |.| semi]
            )
          else 
            val arg = ci.params.head.unjust.fst.cppName
            vcat(
              (if !crepr.is-conAsJust then [] else ["if kk_likely(!kk_box_is_maybe".text |.| arguments([arg]) |.| ") { return kk_datatype_as_Just(".text |.| arg |.| "); }".text])
              ++ ["struct".text |+| nameDoc |.| "*".text |+| "=".text |+| "kk_block_alloc_at_as".text |.| 
                arguments([
                  "struct".text |+| nameDoc,
                  (if drepr.is-dataAsMaybe || conFields.is-cons /* open singleton */ then "kk_reuse_null".text else at.cppName),
                  scanCount.pretty |+| "/* scan count*/".text,
                  (if hasCPath then cpath.cppName else "0".text),
                  (if !drepr.is-dataOpen then ctag else "KK_TAG_OPEN".text)
                ]) |.| semi]
              ++ (if !drepr.is-dataOpen then [] else [tmp |.| "->_base._tag = kk_string_dup".text |.| arguments([ctag]) |.| semi])
              ++ conFields.map(fn(cf) cf.assignField(fn(fld) tmp |.| "->".text |.| fld))
              ++ paddingFields.map(fn((padding, _)) tmp |.| "->".text |.| padding.ppDefName |+| "= kk_box_null();".text)
              ++ ["return".text |+| ci.conBaseCastName |.| arguments([tmp]) |.| semi]
            )
    )
  )
  ()

fun genConstructorBaseCast(ci: conInfo, crepr: conRepr, info: dataInfo, drepr: dataRepr)
  match crepr
    ConEnum -> ()
    ConSingleton -> ()
    ConIso -> ()
    _ | drepr.isValue -> ()
    _ ->
      emitToH("static inline".text |+| info.name.typeClassName.cppName |+| ci.conBaseCastName |.|
      parameters(["struct".text |+| ci.name.cppName |.| "* _x".text]) |+|
      block("return".text |+| "kk_datatype_from_base".text |.| arguments(["&_x->_base".text]) |.| semi))

fun genConstructorAccess(ci: conInfo, crepr: conRepr, info: dataInfo, drepr: dataRepr)
  if drepr.isValue || crepr.is-conSingleton then ()
  else
    emitToH("static inline struct".text |+| ci.name.cppName |.| "*".text |+| ci.conAsName |.|
      parameters([info.name.typeClassName.cppName |+| "x".text]) |+|
      block(
        "return".text |+| "kk_datatype_as_assert".text |.|
        arguments(["struct".text |+| ci.name.cppName |.| "*".text, "x".text, (if drepr.is-dataOpen then "KK_TAG_OPEN".text else ppConTag(ci, crepr, drepr))]) 
        |.| semi
      )
    )
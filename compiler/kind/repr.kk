import compiler/common/name
import compiler/common/name-prim
import compiler/common/syntax
import compiler/common/failure
import compiler/type/type

// Create a datadef and elaborate conInfo's with a ValueRepr
// and correctly ordered fields depending on alignment
// constraints and platform sizes.

// value types
fun createDataDef(emitError: (string) -> e (), emitWarning: (string) -> e (), lookupDataInfo: (name) -> e maybe<dataInfo>, platform: platform, nm:name, resultHasKindStar: bool, isRec: bool, sort: dataKind, extraFields: int, defaultDef:dataDef, conInfos0: list<conInfo>): e (dataDef, list<conInfo>)
  val isVal = defaultDef.isValue
  fun createConInfoRepr(c: conInfo)
    val (orderedFields, vrepr) = orderConFields(emitError, "constructor " ++ (c.name:name).show, lookupDataInfo, platform, extraFields, c.params)
    c(orderedParams=orderedFields, valueRepr=vrepr)
  
  // (m = raw, n = scan)
  fun maxDataDefs(ddfs)
    match ddfs
      Nil ->
        if !isVal then DataDefNormal // reference type no constructors
        else
          val size = 
            if nm == nameTpChar || nm == nameTpInt32 || nm == nameTpFloat32 then 4
            elif nm == nameTpFloat || nm == nameTpInt64 then 8
            elif nm == nameTpInt8 then 1
            elif nm == nameTpInt16 || nm == nameTpFloat16 then 2
            elif nm == nameTpAny || nm == nameTpFieldAddr || nm == nameTpIntPtrT then platform.ptrSize
            elif nm == nameTpSSizeT then platform.sizeSize
            else 0
          val m =
            if size <= 0 then
              emitWarning("is declared as a primitive value type but has no known compilation size, assuming size" ++ platform.ptrSize.show)
              platform.ptrSize
            else size
          DataDefValue(ValueRepr(m, 0, m))
      [vr] -> DataDefValue(vr)
      Cons(vr, vrs) ->
        val dd = vrs.maxDataDefs
        match (vr, dd)
          (ValueRepr(0, 0), DataDefValue(v)) -> DataDefValue(v)
          (v, DataDefValue(ValueRepr(0, 0))) -> DataDefValue(v)
          (ValueRepr(m1, 0, a1), DataDefValue(ValueRepr(m2, 0, a2))) ->
            DataDefValue(ValueRepr(m1.max(m2), 0, a1.max(a2)))
          (ValueRepr(0, n1, a1), DataDefValue(ValueRepr(0, n2, a2))) ->
            DataDefValue(ValueRepr(0, n1.max(n2), a1.max(a2)))
          (ValueRepr(m1, n1, a1), DataDefValue(ValueRepr(m2, n2, a2))) 
            // equal scan fields
            | n1 == n2 -> DataDefValue(ValueRepr(m1.max(m2), n1, a1.max(a2)))
            | True ->
              if isVal then
                emitError("is declared as a value type but has\n"++
                  "multiple constructors with different number of regular types overlapping with value types.\n" ++
                  "hint: value types with multiple constructors must all use the same number of regular types (use 'box' to use a value type as a regular type)." )
              DataDefNormal
          _ -> DataDefNormal

  fun createMaxDataDef(ci: list<conInfo>)
    val vreprs = ci.map(valueRepr)
    val ddef = maxDataDefs(vreprs)
    match ddef
      DataDefValue(ValueRepr(0, 0, 0)) -> // enum
        val n = ci.length
        if n < 256 then DataDefValue(valueReprRaw(1)) // uint8
        elif n < 65536 then DataDefValue(valueReprRaw(2)) // uint16
        else DataDefValue(valueReprRaw(4)) // uint32
      _ -> ddef

  // calculate the value repr of each constructor
  val conInfos = conInfos0.map(createConInfoRepr)

  // datadef
  val maxMembers = conInfos.map(fn(i) i.params.length).maximum()
  val conCount = conInfos.length
  val canbeValue = resultHasKindStar && !sort.is-retractive
  val isEnum = canbeValue && maxMembers == 0 && conCount >= 1
  val isIso = canbeValue && maxMembers == 1 && conCount == 1
  
  val ddef = match defaultDef
    DataDefOpen -> defaultDef
    DataDefRec -> defaultDef
    DataDefNormal | isRec -> DataDefRec
    DataDefNormal -> 
      val dd = conInfos.createMaxDataDef
      // match dd
      //   DataDefValue | isEnum -> dd // allow allocated enums
      //   DataDefValue | isIso -> dd // iso type are always value types
      DataDefNormal
    DataDefAuto | isRec -> DataDefRec
    DataDefAuto ->
      val dd = conInfos.createMaxDataDef
      match dd
        DataDefValue | isEnum -> dd
        DataDefValue | isIso -> dd // iso types are preferred as value types
        DataDefValue(vr) ->
          val wouldGetTagField = conCount > 1 && !isEnum
          val size = platform.size(vr) + (if wouldGetTagField then platform.fieldSize else 0)
          if (size <= 2*platform.ptrSize && (maxMembers < 3 && canbeValue)) then
            emitWarning("may be better declared as a value type for efficiency (e.g. 'value type/struct'),\n" ++
              "or declared as a reference type to suppress this warning (e.g. 'ref type/struct')")
          DataDefNormal
        _ -> DataDefNormal
    DataDefValue | isRec ->
      emitError("cannot be declared as value type since it is recursive.")
      DataDefNormal
    DataDefValue | !resultHasKindStar ->
      emitError("is declared as a value type but does not have value kind ('V').")
      DataDefNormal
    DataDefValue | sort.is-retractive ->
      emitError("is declared as a value type but is not (co)inductive.")
      DataDefNormal
    DataDefValue ->
      val dd = conInfos.createMaxDataDef()
      match dd
        DataDefValue(vr) ->
          val size = platform.size(vr)
          if size > 4*platform.ptrSize then
            emitWarning("requires " ++ size.show ++ " bytes which is rather large for a value type")
          if isEnum then
            emitWarning("is an enumeration -- there is not need to declare it as a value type")
          dd
        _ ->
          // should never happen
          emitError("cannot be used as a value type.") 
          DataDefNormal
  (ddef, conInfos)

// Determine the size of a constructor
//  order constructor fields of constructors with raw field so the regular fields come first to be scanned.
// return the ordered fields, and a ValueRepr (raw size part, the scan count (including tags), align, and full size)
// The size is used for reuse and should include all needed fields including the tag field for "open" datatypes 
fun orderConFields(emitError: (string) -> e (), nameDoc: string, getDataInfo: (name) -> e maybe<dataInfo>, platform: platform, extraPreScan: int, fields: list<(name, ktype)>): e (list<(name, ktype)>, valueRepr)
  fun visit(rraw: list<((name, ktype), valueRepr)>, rmixed: list<((name, ktype), valueRepr)>, rscan: list<(name, ktype)>, scanCount0: int, alignment0: int, l: list<(name, ktype)>)
    if rmixed.length > 1 then
      emitError(nameDoc ++ " has multiple value type fields that each contain both raw types and regular types\n" ++
        "hint: use 'box' on either field to make it a non-value type.")
    // size before any mixed and raw fields
    val preSize = platform.headerSize + scanCount0 * platform.fieldSize
    // if there is a mixed value member (with scan fields) we may need to add padding scan fields (!)
    // (or otherwise the C compiler may insert uninitialized padding)
    val (padding, mixedScan) =
      match rmixed
        Cons((_, ValueRepr(_, scan, ralign))) ->
          val padSize = preSize % ralign
          val padCount = padSize / platform.fieldSize
          if (padSize % platform.fieldSize) != 0 then
            trace("kind/info orderConFields: illegal alignment " ++ ralign.show)
          (list(1, padCount - 1).map(fn(i) ((newPaddingName(scanCount0 + i), typeAny), valueReprScan(1))), scan + padCount)
        _ -> (Nil, 0)
    // calculate the rest now
    val scanCount = scanCount0 + mixedScan
    val alignment = if scanCount > 0 then alignment0.max(platform.fieldSize) else alignment0
    val rest = padding ++ rmixed ++ rraw.reverse
    val restSizes = rest.map(fn((_, vr)) platform.size(vr))
    val restFields = rest.map(fst)
    val size = alignedSum(preSize, restSizes)
    val rawSize = size - platform.headerSize - (scanCount * platform.fieldSize)
    val vrepr = ValueRepr(rawSize, scanCount, alignment)
    (rscan.reverse ++ restFields, vrepr)
  visit([], [], [], extraPreScan, 0, fields)

fun extractDataDefType(tp: ktype): maybe<name>
  match tp
    TApp(t) -> t.extractDataDefType
    TForAll(_, _, t) -> t.extractDataDefType
    TCon(tc) -> Just(tc.name)
    _ -> Nothing

// Return the DataDef for a type.
// This may be 'Nothing' for abstract types.
fun getDataDef(lookupDI: (name) -> e maybe<dataInfo>, tp: ktype): e maybe<dataDef>
  match tp.extractDataDefType
    Nothing -> Just(DataDefNormal)
    Just(nm) | nm == nameTpBox -> Just(DataDefNormal)
    Just(nm) ->
      val mdi = lookupDI(nm)
      match mdi
        Nothing -> Nothing
        Just(di) -> Just(di.def)

import compiler/core/core
import compiler/common/syntax
import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/common/nice
import compiler/core/corevar
import compiler/core/borrowed
import compiler/type/type
import compiler/type/pretty
import compiler/type/typevar
import compiler/kind/kind
import compiler/kind/newtypes
import compiler/lib/pprint
import compiler/platform/config
import compiler/common/file
import compiler/lib/printer
import compiler/backend/c/helpers
import std/os/path
import newstd/data/linearset
import newstd/data/sort

val externalNames = [(exprTrue.conName, "true"), (exprFalse.conName, "false")]

// Generate C code from System-F core language
fun cFromCore(cTarget: cTarget, b: buildType, sourceDir: path, 
              platform: platform, borrowed: borrowed, enableReuse: bool, 
              enableSpecialize: bool, enableReuseSpecialize: bool, enableBorrowInference: bool, 
              eagerPatBind: bool, stackSize: int, mbMain: maybe<(name, bool)>, 
              core: core): <pure,compFlags,uniquePhase,newtypes,printer,documentation,coreOptions,niceEff,prettyTypeEff,precEff> (doc, doc, core)
  with handler
    val cdefToHeader = False
    val substEnv = []
    val cdefName = core.coreName
  var rhdoc := []
  var rcdoc := []
  var ridoc := [] // initialization expressions
  var rtdoc := [] // toplevel (goes to either H or C)
  var rddoc := [] // done expressions
  var canonicalLamTypes := linearSet([], fn(c1: canonicalLambda, c2: canonicalLambda) c1 == c2, show)
  with handler
    fun emitToH(d: doc) rhdoc := Cons(d, rhdoc)
    fun emitToC(d: doc) rcdoc := Cons(d, rcdoc)
    fun emitToInit(d: doc) ridoc := Cons(d, ridoc)
    fun emitToTop(d: doc) rtdoc := Cons(d, rtdoc)
    fun emitToDone(d: doc) rddoc := Cons(d, rddoc)
    fun getInit() ridoc.vcat
    fun getDone() rddoc.vcat
    fun getTop() 
      val res = rtdoc.reverse.vcat
      rtdoc := []
      res
    fun addCanonical(c: canonicalLambda) 
      if canonicalLamTypes.member(c) then False
      else
        canonicalLamTypes := canonicalLamTypes.add(c)
        True
    val modName = core.coreName
    val prettyModName = core.coreName.ppModName
    val targetPlatform = platform
    val eagerPatBind = eagerPatBind
    val enableReuse = enableReuse
    val enableSpecialize = enableSpecialize
    val enableReuseSpecialize = enableReuseSpecialize
    val enableBorrowInference = enableBorrowInference
    val cTarget = cTarget
    val borrowed = borrowed
    val stackSize = stackSize
    val sourceDir = sourceDir
    val buildType = b
    val debug = False
  (rcdoc.vcat, rhdoc.vcat, genModule(core, mbMain))

val checkInitDoc = [
  "static bool _kk_initialized = false;".text,
  "if (_kk_initialized) return;".text,
  "_kk_initialized = true;".text].vcat

fun initImport(i: kimport)
  i.importName.qualify(".init".newName).cppName |.| emptyArgs |.| semi

fun doneImport(i: kimport)
  i.importName.qualify(".done".newName).cppName |.| emptyArgs |.| semi

val customInitDoc = [
  "#if defined(KK_CUSTOM_INIT)".text,
  "  KK_CUSTOM_INIT".text |+| emptyArgs |.| semi,
  "#endif".text].vcat

fun genModule(core: core, mbMain: maybe<(name, bool)>): asmEff core
  // boxCore
  // borrowedExtend
  // parcCore
  // parcReuseCore
  // parcReuseSpecializeCore

  val headComment = "// Koka generated module:".text |+| modName.show.pretty |+| ", koka version:".text |+| compFlags.version.pretty |.| ", platform:".text |+| (targetPlatform.ptrSize * 8).pretty |.| "-bit".text
  val initSignature = "void".text |+| ".init".newName.qualify(modName).cppName |.| emptyParams
  val doneSignature = "void".text |+| ".done".newName.qualify(modName).cppName |.| emptyParams

  [checkInitDoc, core.imports.map(initImport).vcat, customInitDoc].vcat.emitToInit
  
  core.imports.reverse.map(doneImport).vcat.emitToDone

  emitToC(
    vcat([
      headComment,
      "#include".text |+| dquotes(modName.moduleNameToPath.text) |.| ".h".text] ++ 
      core.externals.map(importExternalInclude).concat ++ 
      core.externals.map(includeExternalC).concat
    ))
  
  emitToH(
    vcat([
      "#pragma once".text,
      "ifndef ".text |.| prettyModName |.| "_H".text,
      "define ".text |.| prettyModName |.| "_H".text,
      headComment,
      "#include <kklib.h>".text] ++ 
      core.imports.map(moduleImport) ++ 
      core.externals.map(includeExternalH).concat
    ))

  emitToH(
    linebreak |.| 
    "// type declarations".text)

  genTypeDefs(core.typeDefs)
  emitToH(
    linebreak |.| 
    "// value declarations".text)

  genTopGroups(core.defs)

  genMain(mbMain)

  emitToDone(
    vcat([
      "static bool _kk_done = false;".text,
      "if (_kk_done) return;".text,
      "_kk_done = true;".text,
      empty,
      "#if defined(KK_CUSTOM_DONE)".text,
      "  KK_CUSTOM_DONE".text |+| emptyArgs |.| semi,
      "#endif".text,
    ]))

  val init = getInit()
  val done = getDone()
  emitToC(
    linebreak |.| 
    "// initialization".text |-|
    initSignature |.|
    init.block |-|
    "\n// termination".text |-|
    doneSignature |.|
    done.block)
  
  emitToH(
    vcat([
      linebreak |.| initSignature |.| semi |.| linebreak,
      linebreak |.| doneSignature |.| semi |.| linebreak] ++
      core.externals.map(includeEndExternalH).concat ++
      ["#endif // header".text]
    ))
  core

// TODO: more
fun moduleImport(imp: kimport): doc
  "#include".text |+|
  (if imp.package == "" then dquotes(imp.importName.moduleNameToPath.text |.| ".h".text)
  else brackets(imp.package.text) |.| "/".text |.| imp.importName.moduleNameToPath.text |.| ".h".text)

fun includeExternalC(ext: external)
  match externalImportLookup(C(cTarget), buildType, "include-inline", ext)
    Just(content) -> [content.list.drop-while(isSpace).string.text]
    _ -> []

fun includeExternalH(ext: external)
  match externalImportLookup(C(cTarget), buildType, "header-include-inline", ext)
    Just(content) -> [content.list.drop-while(isSpace).string.text]
    _ -> []

fun includeEndExternalH(ext: external)
  match externalImportLookup(C(cTarget), buildType, "header-end-include-inline", ext)
    Just(content) -> [content.list.drop-while(isSpace).string.text]
    _ -> []

fun importExternalInclude(ext: external): asmEff list<doc>
  match externalImportLookup(C(cTarget),buildType,"include",ext)
    Just(includePath) -> 
      [
        "#include".text |+| 
        (
          if includePath.head-char.map(fn(x) x=='<').is-just then includePath.text 
          else 
            dquotes(
              if sourceDir.string == "" then includePath.text 
              else (sourceDir / includePath.path).normalize.string.text)
      )]
    _ -> []

fun genMain(mbMain: maybe<(name, bool)>): asmEff ()
  match mbMain
    Nothing -> ()
    Just((name, _)) ->
      emitToC(
        "\n// main exit\n static void _kk_main_exit(void)".text |+| block(
          vcat([
            "kk_context_t* _ctx = kk_get_context();".text,
            cppName(modName.qualify(".done".newName)) |.| parens("_ctx".text) |.| semi
          ])
        ) |-|
        "\n// main entry \nint main(int argc, char** argv)".text |+| block(vcat([
          text("kk_assert(sizeof(size_t) == " ++ targetPlatform.sizeSize.show ++ " && sizeof(void*) == " ++ targetPlatform.ptrSize.show ++ ");"),
          (if stackSize == 0 then empty else ("kk_os_set_stack_size(KK_IZ(" ++ stackSize.show ++ "));").text),
          "kk_context_t* _ctx = kk_main_start(argc, argv);".text,
          cppName(modName.qualify(".init".newName)) |.| parens("_ctx".text) |.| semi,
          "atexit(&_kk_main_exit);".text,
          cppName(name) |.| parens("_ctx".text) |.| semi,
          cppName(modName.qualify(".done".newName)) |.| parens("_ctx".text) |.| semi,
          "kk_main_end(_ctx);".text,
          "return 0;".text
        ]))
      )

fun genLocalGroups(dgs: defGroups): asmEff list<doc>
  dgs.map(genLocalGroup)

fun genLocalGroup(dg: defGroup): asmEff doc
  match dg
    DefRec -> fail("backend/c/from-core genLocalGroup: local recursive function definitions are not allowed")
    DefNonRec(d) -> genLocalDef(d)

fun genLocalDef(d: def): asmEff doc
  val resDoc = typeComment(d.ktype.cppType)
  val defDoc = genStat(ResultAssign(d.defTName, Nothing), d.defExpr)
  fun isDiscardExpr(e: expr)
    e.isUnit || e.isReuseNull
  vcat([
    (if d.doc == "" then empty else align(vcat(Cons(space, d.doc.trimComment.lines.map(text)))))
    ] ++ (if d.defName.isNil && defDoc.dStartsWith(d.defName.show ++ " =") then
     // single assignment without declarations
        [d.ktype.cppType |+| defDoc |.| semi] 
      else
        [(if d.defName.isNil then empty else ppVarDecl(d.defTName) |.| d.ktype.unitSemi),
         (if d.defExpr.isDiscardExpr then empty else defDoc)]
     )
  )

fun isWhitespace(c: char)
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

fun trimComment(comm: string)
  fun trimRest(xs: list<char>)
    xs.drop-while(fn(x) x.isWhitespace).reverse.string
  fun trimLine(s: string)
    match s.list.reverse
      Cons('\\', xs) -> xs.trimRest
      xs -> xs.trimRest
  comm.lines.map(trimLine).unlines

fun unitSemi(tp: ktype): doc
  if tp.isTypeUnit then " = kk_Unit;".text else semi


// Generate C declaration for top level definitions

fun genTopGroups(d: list<defGroup>): asmEff ()
  with localUnique
  d.map(genTopGroup)
  ()

fun genTopGroup(g: defGroup): asmEff ()
  match g
    DefRec(defs) -> 
      defs.map(genFunTopDefSig)
      defs.map(fn(d) d.genTopDef(False, False))
      ()
    DefNonRec(d) ->
      val inlineC = d.kinline.is-inlineAlways || d.isInlineable(5)
      d.genTopDef(True, inlineC)

fun genFunTopDefSig(d: def)
  emitToH(
    linebreak |.| d.genFunDefSig(False) |.| semi |+|
    d.ktype.cppType.typeComment
  )

fun genFunDefSig(d: def, inlineC: bool)
  d.defExpr.genFunSig(inlineC, d.vis, d.defName)

fun genFunSig(ex: expr, inlineC: bool, vis: visibility, nm: name)
  match ex
    TypeApp(e) -> e.genFunSig(inlineC, vis, nm)
    TypeLam(_, e) -> e.genFunSig(inlineC, vis, nm)
    Lam(params, _, body) -> body.genLamSig(inlineC, vis, nm, params)
    _ -> fail("backend/c/from-core genFunSig: expected lambda expression")

fun genLamSig(body: expr, inlineC: bool, vis: visibility, nm: name, params: list<tName>)
  val inl = if inlineC then "static inline ".text else empty
  inl |.| body.typeOf.cppType |+| nm.cppName |.| params.tParameters

fun genTopDef(d: def, genSig: bool, inlineC: bool)
  if d.doc != "" then
    val doc = align(vcat(Cons(space, d.doc.trimComment.lines.map(text))))
    if inlineC then emitToH(doc) else emitToC(doc)
  d.genTopDefDecl(genSig, inlineC)

fun genTopDefDecl(d: def, genSig: bool, inlineC: bool)
  if d.ktype.isValueOperation then () // Don't generate code for phantom definitions for value operations (these were only needed for type checking)
  else
    val emit = if inlineC then emitToH else emitToC
    val resTp = match d.ktype.splitFunScheme
      Nothing -> d.ktype
      Just((_, _, _, _, res)) -> res
    fun genFunDef(body: expr, params: list<tName>)
      val args = params.map(fn(p) p.getName.cppName)
      val isTailCall = body.isTailCalling(d.defName)
      val bodyDoc = genStat(ResultReturn(Just(TName(d.defName, resTp)), params), body)
      val tpDoc = d.ktype.cppType.typeComment
      val sig = body.genLamSig(inlineC, d.vis, d.defName, params)
      if genSig && !inlineC then emitToH(linebreak |.| sig |.| semi |+| tpDoc)
      val top = getTop() // get top level decls generated by body (for functions etc)
      emit(linebreak |.| top |.| sig |+| (if isTailCall then tcoBlock(tpDoc, bodyDoc) else debugComment("genFunDef: no tail calls to " ++ d.defName.showName ++ " found") |.| tblock(tpDoc, bodyDoc)))

    fun genDecl(ex: expr)
      match ex
        TypeApp(e) -> genDecl(e)
        TypeLam(_, e) -> genDecl(e)
        Lam(params, _, body) | d.sort.is-defFun -> body.genFunDef(params)
        _ | d.sort.is-defFun -> 
          // some optimization turned a toplevel lambda into a value;
          // wrap it back into a lmabda again as all occurences will have InfoArity and call it directly (so it cannot be a function_t)
          match d.ktype.splitFunScheme
            Nothing -> fail("backend/c/from-core genTopDefDecl: expected function type, got: " ++ d.ktype.show ++ " for def " ++ d.defName.show)
            Just((_, _, argTps, _, _)) ->
              val names = list(1, argTps.length).map(fn(x) ("x" ++ x.show).newVarName)
              val tnames = zip(names, argTps).map(fn((nm, (_, tp))) TName(nm, tp))
              val app = App(ex, tnames.map(fn(tn) Var(tn, InfoNone)))
              app.genFunDef(tnames)
        // Special case string literals
        ELit(LitString(s)) -> s.genTopLevelStringLiteral(d.defName, d.vis)
        // Special case for doubles
        ELit(lit as LitFloat) ->
          emitToH("#define".text |+| d.defName.cppName |+| parens("(double)".text |.| lit.ppLit.parens))
        _ ->
          val doc = genStat(ResultAssign(TName(d.defName, d.ktype), Nothing), d.defExpr)
          emitToInit(doc.block) // must be scoped to avoid name clashes
          match d.defName.cppName.genDupDropCall(False, d.ktype)
            [] -> ()
            docs -> emitToDone(docs.hcat |.| semi)
          val hdecl = d.ktype.cppType |+| d.defName.cppName |.| semi
          val cdecl = d.ktype.cppType |+| d.defName.cppName |.| d.ktype.unitSemi
          emitToH(linebreak |.| "extern".text |+| hdecl)
          emitToC(linebreak |.| cdecl)
    with setDef(d.defName, inlineC)
    genDecl(d.defExpr)

fun genTopLevelStringLiteral(s: string, name: name, vis: visibility)
  val (cstr, clen) = s.cString
  val decl = if vis.is-public then empty else "static".text
  val nameDoc = name.cppName
  if clen > 0 then
    emitToC("kk_declare_string_literal".text |.| [decl, nameDoc, clen.pretty, cstr].tupled)
    emitToInit("kk_init_string_literal".text |.| [nameDoc].arguments)
    // TODO: Emit drop in Done?
  else
    emitToC("kk_define_string_literal_empty".text |.| [decl, nameDoc].tupled)
  if vis.is-public then
    emitToH(linebreak |.| "extern".text |+| typeString.cppType |+| nameDoc |.| semi)

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
      emitToH(ci.vis.ppVis |.| "struct".text |+| ci.name.cppName |+| 
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
// TODO: Implement
  ()

fun genConstructorBaseCast(ci: conInfo, crepr: conRepr, info: dataInfo, drepr: dataRepr)
  match crepr
    ConEnum -> ()
    ConSingleton -> ()
    ConIso -> ()
    _ | drepr.isValue -> ()
    _ ->
      emitToH("static inline".text |+| info.name.typeClassName.cppName |+| ci.conBaseCastNameInfo |.|
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

fun genBoxUnbox(nm: name, info: dataInfo, drepr: dataRepr)
  val tname = nm.typeClassName
  tname.genBox(info, drepr)
  tname.genUnbox(info, drepr)

fun genBoxCall(tp: ktype, arg: doc)
  val prim = "box"
  match tp.cType
    CFun -> primName_t(prim, "function_t") |.| tupled([arg, contextDoc])
    CPrim(v) | v == "kk_unit_t" || v == "bool" || v == "kk_string_t" -> primName_t(prim, v) |.| parens(arg)
    CData(nm) -> primName(prim, nm.cppName) |.| tupled([arg, contextDoc])
    _ -> primName_t(prim, tp.cppType.show) |.| tupled([arg, contextDoc])

fun genBox(nm: name, info: dataInfo, drepr: dataRepr)
  // TODO: Implement
  ()

fun genUnbox(nm: name, info: dataInfo, drepr: dataRepr)
  // TODO: Implement
  ()

fun genDupDropCall(nm: doc, isDup: bool, tp: ktype): list<doc>
  // TODO: Implement
  []

fun genDupDrop(nm: name, info: dataInfo, drepr: dataRepr, conInfos: list<(conInfo, conRepr, list<(name, ktype)>, int)>)
  // TODO: Implement
  ()

fun conBaseCastNameInfo(ci: conInfo): doc
  //TODO: Implement
  empty

type result
  ResultReturn(tn: maybe<tName>, args: list<tName>) // first field carries function name if not anonymous and second the arguments which are always known
  ResultAssign(tn: tName, label: maybe<name>) // variable name nad optional label to break

fun genStat(res: result, ex: expr): doc
  empty







// TODO: more here


// Externals

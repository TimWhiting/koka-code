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
import compiler/kind/kind
import compiler/kind/newtypes
import compiler/kind/repr
import compiler/lib/pprint
import compiler/platform/config
import compiler/common/file
import compiler/lib/printer
import compiler/backend/c/helpers
import compiler/backend/c/dup-drops
import compiler/backend/c/constructors
import std/os/path
import newstd/data/linearset

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
          match genDupDropCall(False, d.ktype, d.defName.cppName)
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


fun genLambda(body: expr, params: list<tName>, eff: ktype)
  val fnName = "fun".newDefVarName
  val newLamName = "new-".prepend(fnName)
  val fnTpName = "_t".postpend(fnName)
  val fnTpDoc = fnTpName.cppName
  val structDoc = "struct".text |+| fnTpDoc
  val freeVars = Lam(params, eff, body).freeLocals.list.map(fn(TName(nm, tp)) (nm, tp))
  fun emitError(d: doc)
    fail("backend/c/genLambda: " ++ d.show)
  val nameDoc = (cdefName.show ++ ".<lambda>").text
  fun getDataInfo(nm)
    newtypesLookupAny(nm)
  val (allFields, vrepr) = orderConFields(emitError, nameDoc, getDataInfo, targetPlatform, 1, freeVars)
  val scanCount = vrepr.scanCount
  val (paddingFields, fields) = allFields.partition(fn(f) f.fst.isPaddingName)
  val types = allFields.map(snd)
  val canonicalName = newCanonicalVarName("lambda" ++ (if fields.is-nil then "" else "-") ++ types.map(fn(t) t.cppType.asString).join("-"))
  val canonicalNewName = "new-".prepend(canonicalName)
  val canonicalFunTpName = "_t".postpend(canonicalName)
  val canonicalStructDoc = "struct".text |+| canonicalFunTpName.cppName
  val canonicalFieldNames = zip(allFields, list(1, allFields.length)).map(fn((nmTp, i)) (newName("field-" ++ i.show), nmTp.fst.isPaddingName))
  val canonicalFields = canonicalFieldNames.map(fst).zip(types)
  val canonicalFieldsMap = zip3(canonicalFieldNames.filter(fn(s) !s.snd).map(fst), fields.map(fst), types)
  val canonical = CanonicalLambda(canonicalName, canonicalFieldNames)
  val alreadyGenerated = addCanonical(canonical)
  if !alreadyGenerated && fields.is-cons then
    val tpDecl = "struct".text |+| canonicalFunTpName.cppName |+| block(
      vcat(["struct kk_function_s _base;".text] ++ canonicalFields.map(fn((nm, tp)) tp.cppType |+| nm.cppName |.| semi))
    ) |.| semi
    val newDef = (if cdefToHeader then "static inline" else "static").text |+| 
      "kk_function_t".text |+| canonicalNewName.cppName |.| canonicalFields.closFnParameters |+| block(
        vcat([
          canonicalStructDoc |.| "* _self = kk_function_alloc_as".text |.| arguments([canonicalStructDoc, scanCount.pretty]) |.| semi,
          "_self->_base.fun = kk_kkfun_ptr_box(fnPtr, kk_context());".text
        ] ++ canonicalFieldNames.filter(fn(f) !f.snd).map(fn(f) "_self->".text |.| f.fst.cppName |+| "=".text |+| f.fst.cppName |.| semi)
         ++ canonicalFieldNames.filter(snd).map(fn(f) "_self->".text |.| f.fst.cppName |+| "= kk_box_null();".text)
         ++ ["return kk_datatype_from_base(&_self->_base, kk_context());".text]
        )
      )
    emitToH(vcat([linebreak, "// canonical lambda".text, tpDecl, newDef]) |.| linebreak)
  
  val tpDecl = (if fields.is-nil then "".text else "typedef struct".text) |+| canonicalFunTpName.cppName |+| fnTpName.cppName |.| semi
  val funSig = text(if cdefToHeader then "extern" else "static") |+| body.typeOf.cppType |+| fnName.cppName |.| parameters(["kk_function_t _fself".text] ++ params.map(fn(TName(nm, tp)) tp.cppType |+| nm.cppName))
  val newDef = funSig |.| semi |-| (if fields.is-cons || cdefToHeader then "static inline" else "static").text |+|
    "kk_function_t".text |+| newLamName.cppName |.| ntParameters(fields) |+| block(vcat(
      (
       if fields.is-nil then 
        ["kk_define_static_function".text |.| arguments(["_fself".text, fnName.cppName]), "return kk_function_dup(_fself, kk_context());".text]
       else 
        ["return".text |+| canonicalNewName.cppName |.| arguments(Cons("&".text |.| fnName.cppName, fields.map(fn(f) f.fst.cppName))) |.| semi]
      )))
  emitToCurrentDef(vcat([linebreak, "// lift anonymous function".text, tpDecl, newDef]) |.| linebreak)
  val bodyDoc = genStat(ResultReturn(Nothing, params), body)
  if fields.is-nil then 
    emitToC(funSig |+| block("kk_unused(_fself);".text) |-| bodyDoc)
  else 
    val dups = braces(fields.map(fn((nm, tp)) genDupCall(tp, nm.cppName) |.| semi).hcat)
    emitToC(funSig |+| block(
      vcat(
        [fnTpDoc |.| "* _self = kk_function_as".text |.| arguments([fnTpDoc |.| "*".text, "_fself".text]) |.| semi] ++
        canonicalFieldsMap.map(fn((nmCanon, nm, tp)) tp.cppType |+| nm.cppName |+| "= _self->".text |.| nmCanon.cppName |.| semi |+| "/*".text |+| tp.pretty |+| "*/".text) ++
        ["kk_drop_match".text |.| arguments(["_self".text, dups,"{}".text])]
      )
      |-| bodyDoc
    ))
  val funNew = newLamName.cppName |.| arguments(fields.map(fst).map(cppName))
  funNew

fun zip3(l1: list<a>, l2: list<b>, l3: list<c>): list<(a,b,c)>
  match (l1, l2, l3)
    (Cons(x1, xs1), Cons(x2, xs2), Cons(x3, xs3)) -> Cons((x1, x2, x3), zip3(xs1.unsafe-decreasing, xs2, xs3))
    _ -> Nil

fun genStat(res: result, ex: expr): doc
  empty







// TODO: more here


// Externals

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
import compiler/backend/c/expr
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

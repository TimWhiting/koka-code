//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

import compiler/common/name
import compiler/common/syntax
import compiler/common/failure
import std/core/unsafe

//---------------------------------
// Special
//---------------------------------
val nameExpr        = "@expr".new-name
val nameType        = "@type".new-name

val nameInteractiveModule  = "interactive".new-module-name

val nameMain        = "@main".new-name
val nameCopy        = "@copy".new-name
val nameOpExpr      = "@opexpr".new-name

fun copy-name-of(typename: name): <comp-flags,exn> name
  qualify(typename.qualifier, typename.unqualify.name-as-module-name.qualify-locally(nameCopy))

//---------------------------------
// Primitive operations
//---------------------------------
val nameIf          = "if".new-name
val nameCase        = "case".new-name

//---------------------------------
// Core
//---------------------------------
val nameTpIO = "io".prelude-name
val nameTpNamed     = "nmd".prelude-name
val nameTpScope     = "scope".prelude-name
val nameTpPure      = "pure".prelude-name

val nameTpAsync     = "std/async".new-qualified("async")
val nameTpAsyncX    = "std/async".new-qualified("asyncx")
val nameTpBuilder   = "std/text/string".new-qualified("builder")
val nameTpArray     = "std/data/array".new-qualified("array")
val nameTpMDict     = nameDict.qualify("mdict".new-name)
val nameTpDict      = nameDict.qualify("dict".new-name)

val nameTpDelay          = "delay".prelude-name
val nameMainConsole      = "main-console".prelude-name

val nameSubStr1          = "substr1".core-string-name
val namesSameSize   = ["id","map","reverse","foldl","foldr","filter"].map(prelude-name)

//---------------------------------
// Lists
//---------------------------------
val nameNull        = "Nil".core-types-name
val nameCons        = "Cons".core-types-name
val nameTpList      = "list".core-types-name

//---------------------------------
// std/core/debug
//---------------------------------
val nameAssert      = nameCoreDebug.qualify("assert".new-name)
val nameTrace   = nameCoreDebug.qualify("trace".new-name)
val nameLog     = nameCoreDebug.qualify("log".new-name)

val nameCoreFileFile = nameCoreDebug.qualify(new-locally-qualified("", "file", "kk-file"))
val nameCoreFileLine = nameCoreDebug.qualify(new-locally-qualified("", "file", "kk-line"))
val nameCoreFileModule = nameCoreDebug.qualify(new-locally-qualified("", "file", "kk-module"))

//---------------------------------
// std/core/vector
//---------------------------------
val nameVector      = "unvlist".core-vector-name

//---------------------------------
// std/core/int
//---------------------------------
val nameByte        = "std/core/int".new-qualified("uint8")
val nameInt8        = "std/core/int".new-qualified("int8")
val nameInt16       = "std/core/int".new-qualified("int16")
val nameInt32       = "std/num/int32".new-qualified("int32")
val nameInt64       = "std/num/int64".new-qualified("int64")
val nameSSizeT      = "std/core/int".new-qualified("ssize_t")
val nameIntPtrT     = "std/core/int".new-qualified("intptr_t")

val nameIntAdd      = "int-add".core-int-name
val nameIntSub      = "int-sub".core-int-name

// these are used by evidence in std/core/hnd and can be compiler generated
val nameInternalInt32 = "@make-int32".core-types-name
val nameInternalSSizeT = "@make-ssize_t".core-types-name

// javascript backend
val nameIntConst = "@int-const".core-types-name


//---------------------------------
// std/core/exn
//---------------------------------

val nameTpException  = "exception".core-exn-name
val nameTpPartial   = "exn".core-exn-name
val namePatternMatchError = "error-pattern".core-exn-name

//---------------------------------
// Contexts: std/core/types
//---------------------------------

fun cfield-name(n: string): name
  n.core-types-name()

val nameTpCCtxx           = "cctx".cfield-name
val nameTpCCtx            = "ctx".cfield-name

val nameCCtxCreate        = "@cctx-create".cfield-name
val nameCCtxHoleCreate    = "@cctx-hole-create".cfield-name
val nameCCtxExtend        = "@cctx-extend".cfield-name
val nameCCtxComposeExtend = "@cctx-compose-extend".cfield-name
val nameCCtxSetCtxPath    = "@cctx-setcp".cfield-name

val nameCCtxEmpty         = new-locally-qualified("std/core/types", "cctx", "empty")
val nameCCtxApply         = new-locally-qualified("std/core/types", "cctx", "(++.)")
val nameCCtxCompose       = new-locally-qualified("std/core/types", "cctx", "(++)")

val nameTpFieldAddr       = "@field-addr".cfield-name
val nameFieldAddrOf       = "@field-addr-of".cfield-name

//---------------------------------
// std/core/hnd
//---------------------------------

val nameTpMarker    = "marker".core-hnd-name
val nameTpHTag      = "htag".core-hnd-name
fun name-tp-clause(i:int): name
  ("clause" ++ i.show).core-hnd-name
val nameTpEv        = "ev".core-hnd-name
val nameTpEvv       = "evv".core-hnd-name
val nameTpEvIndex   = "ev-index".core-hnd-name
fun name-clause(sort, i: int): name
  ("clause-" ++ sort ++ i.show).core-hnd-name
val nameTpResumeContext = "resume-context".core-hnd-name

val nameHTag        = "@new-htag".core-hnd-name
fun name-perform(i: int)
  ("@perform" ++ i.show).core-hnd-name
val nameEvvAt       = "@evv-at".core-hnd-name
val nameEvvLookup   = "@evv-lookup".core-hnd-name
val nameEvvIndex    = "@evv-index".core-hnd-name
val nameMaskAt      = "@mask-at".core-hnd-name
val nameMaskBuiltin = "@mask-builtin".core-hnd-name
fun name-open-at(i: int)
  ("@open-at" ++ i.show).core-hnd-name
fun name-open-none(i: int)
  ("@open-none" ++ i.show).core-hnd-name
fun name-open(i: int)
  ("@open" ++ i.show).core-hnd-name
val nameEvvIsAffine = ("@evv-is-affine").core-hnd-name

val nameHandle      = "@hhandle".core-hnd-name
val nameNamedHandle = "@named-handle".core-hnd-name

val nameYielding    = "yielding".core-hnd-name
val nameYieldExtend = "yield-extend".core-hnd-name
val nameBind        = "yield-bind".core-hnd-name // prelude-name  "bind"
val nameBind2       = "yield-bind2".core-hnd-name
val nameEffectOpen  =  "@open".core-types-name // prelude-name "@open"

val nameInitially   = "initially".core-hnd-name
val nameFinally     = "finally".core-hnd-name
fun name-clause-tail-no-op(n: int): e name
  core-hnd-name("clause-tail-noop" ++ show(n))

fun is-clause-tail-name(n: name): maybe<int>
  if n.nameModule != nameCoreHnd.nameModule then Nothing
  else
    val s = n.local
    if s.starts-with("clause-tail").bool then
      s.slice.drop(11).string.parse-int
    else
      Nothing

//---------------------------------
// std/core/types
//---------------------------------

val nameToAny       = "@toany".core-types-name
val nameValueOp     = "@Valueop".core-types-name
val nameTpValueOp   = "@valueop".core-types-name

val nameDecreasing  = nameCoreUndiv.qualify("pretend-decreasing".new-name)
val nameUnsafeTotal = nameCoreUnsafe.qualify("unsafe-total".new-name)

val nameIndex       = "index".new-hidden-name // used for []
val nameReturn      = "return".new-hidden-name
val nameAssign      = "@assign".new-hidden-name // used for :=

val nameRefSet      = "set".core-types-name
val nameLocalSet    = "local-set".core-types-name
val nameLocalGet    = "local-get".core-types-name
val nameDeref       = try({qualify-locally("ref".new-module-name, "!".core-types-name)}).default("error".new-name)
val nameByref       = "@byref".core-types-name

val namePredHeapDiv = "hdiv".core-types-name
val namePredEffDiv  = "ediv".core-types-name

val nameTpRef       = "ref".core-types-name
val nameTpLocalVar  = "local-var".core-types-name
val nameTpLocal     = "local".core-types-name
val nameRef         = "ref".core-types-name
val nameLocalNew    = "local-new".core-types-name
val nameLocal       = "local-var".core-hnd-name
val nameRunLocal    = "local-scope".core-types-name

val nameTpTotal     = nameEffectEmpty // "total"
val nameTpDiv       = "div".core-types-name
val nameTpAlloc     = "alloc".core-types-name
val nameTpRead      = "read".core-types-name
val nameTpWrite     = "write".core-types-name
val nameTpST        = "st".core-types-name

val nameEffectEmpty = "total".core-types-name
val nameEffectExtend= "effect-extend".core-types-name
val nameEffectAppend= "@effect-append".new-name  // only used during kind inference

val nameAnd         = "&&".core-types-name
val nameOr          = "||".core-types-name

fun make-tp-handled(namedh: bool, linear: bool): name
  core-types-name(if namedh then "nhandled" else "handled" ++ (if linear then "1" else ""))

val nameTpHandled   = make-tp-handled(False, False)
val nameTpHandled1  = make-tp-handled(False, True)
val nameTpNHandled  = make-tp-handled(True, False)
val nameTpNHandled1 = make-tp-handled(True, True)

val nameIdentity    = "id".core-types-name

val nameUnit        = "Unit".core-types-name
val nameTrue        = "True".core-types-name
val nameFalse       = "False".core-types-name

val nameJust        = "Just".core-types-name
val nameNothing     = "Nothing".core-types-name
val nameTpMaybe     = "maybe".core-types-name

val nameOptional    = "@Optional".core-types-name
val nameOptionalNone= "@None".core-types-name
val nameTpOptional  = "@optional".core-types-name

val nameTpVoid      = "void".core-types-name
val nameTpUnit      = "unit".core-types-name
val nameTpBool      = "bool".core-types-name
val nameTpInt       = "int".core-types-name

// val nameTpByte      = "uint8".core-types-name
val nameTpInt8      = "int8".core-types-name
val nameTpInt16     = "int16".core-types-name
val nameTpInt32     = "int32".core-types-name
val nameTpInt64     = "int64".core-types-name
val nameTpSSizeT    = "ssize_t".core-types-name
val nameTpIntPtrT   = "intptr_t".core-types-name

val nameTpFloat     = "float64".core-types-name
val nameTpFloat32   = "float32".core-types-name
val nameTpFloat16   = "float16".core-types-name

val nameTpChar      = "char".core-types-name
val nameTpString    = "string".core-types-name
val nameTpAny       = "any".core-types-name
val nameTpVector    = "vector".core-types-name

// These are internal only inserted by the boxing phase
val nameTpBox       = "@Box".core-types-name
val nameBoxCon      = "@Box".core-types-name
val nameBox         = "@box".core-types-name
val nameUnbox       = "@unbox".core-types-name

val nameTpReuse     = "@reuse".core-types-name
val nameReuseNull   = "@no-reuse".core-types-name
val nameDropReuse   = "@drop-reuse".core-types-name
val nameFreeReuse   = "@free-reuse".core-types-name
val nameAllocAt     = "@alloc-at".core-types-name
val nameAssignReuse = "@assign-reuse".core-types-name
val nameReuse       = "@reuse".core-types-name
val nameReuseIsValid= "@reuse-is-valid".core-types-name
val nameConFieldsAssign = "@con-fields-assign".core-types-name
val nameConTagFieldsAssign = "@con-tag-fields-assign".core-types-name
val nameSetTag      = "@set-tag".core-types-name
val nameKeep        = "keep".core-types-name

val nameDup         = "@dup".core-types-name
val nameDrop        = "@drop".core-types-name
val nameFree        = "@free".core-types-name
val nameDecRef      = "@dec-ref".core-types-name
val nameIsUnique    = "@is-unique".core-types-name
val nameKeepMatch   = "@keep-match".core-types-name
val nameDropMatch   = "@drop-match".core-types-name
val nameReuseMatch  = "@reuse-match".core-types-name

val nameReuseDrop   = "@reuse-drop".core-types-name

val nameDropSpecial = "@drop-special".core-types-name

fun name-tuple(n: int): name
  if n <= 1 then nameUnit else ("Tuple" ++ n.show).core-types-name // core-types-name("(" ++ replicate(",", n - 1).join ++ ")")

fun name-tp-tuple(n: int): name
  if n <= 1 then nameTpUnit else ("tuple" ++ n.show).core-types-name // core-types-name("(" ++ replicate(",", n - 1).join ++ ")")

fun is-name-tuple(n: name): bool
  val s = n.local
  n == nameUnit ||   
    n.nameModule == nameCoreTypes.nameModule && s.starts-with("Tuple").bool && s.slice.drop(5).string.list.all(is-digit)

fun is-name-tp-tuple(n: name): bool
  val s = n.local
  n == nameTpUnit ||   
    n.nameModule == nameCoreTypes.nameModule && s.starts-with("tuple").bool && s.slice.drop(5).string.list.all(is-digit)


fun prelude-name(s: string): name
  nameSystemCore.qualify(s.new-name)

fun core-hnd-name(s: string): name
  nameCoreHnd.qualify(s.new-name)
fun core-types-name(s: string): name
  nameCoreTypes.qualify(s.new-name)

fun core-int-name(s: string): name
  new-qualified("std/core/int", s)
fun core-list-name(s: string): name
  new-qualified("std/core/list", s)
fun core-exn-name(s: string): name
  new-qualified("std/core/exn", s)
fun core-vector-name(s: string): name
  new-qualified("std/core/vector", s)
fun core-string-name(s: string): name
  new-qualified("std/core/string", s)

val nameSystemCore  = "std/core".new-module-name
val nameCoreHnd     = "std/core/hnd".new-module-name
val nameCoreUndiv   = "std/core/undiv".new-module-name
val nameCoreUnsafe  = "std/core/unsafe".new-module-name
val nameCoreTypes   = "std/core/types".new-module-name
val nameDict        = "std/data/dict".new-module-name
val nameCoreDebug   = "std/core/debug".new-module-name

fun is-system-core-name(n: name): bool
  val m = n.nameModule
  m == "std/core" || m.starts-with("std/core/").bool

fun is-primitive-name(n: name): bool
  n.qualifier.is-primitive-module

fun is-primitive-module(n: name): bool
  n == nameCoreHnd || n == nameCoreTypes

//---------------------------------
// Primitive Kind Constructors
//---------------------------------
val nameKindStar    = "V".new-name
val nameKindLabel   = "X".new-name
val nameKindFun = "->".new-name
val nameKindPred    = "P".new-name
val nameKindEffect  = "E".new-name
val nameKindHeap    = "H".new-name
val nameKindScope   = "S".new-name
val nameKindHandled = "HX".new-name
val nameKindHandled1 = "HX1".new-name

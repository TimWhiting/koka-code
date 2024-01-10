import compiler/common/name
import compiler/common/syntax

// Special
val nameExpr        = ".expr".new-name
val nameType        = ".type".new-name

val nameInteractiveModule  = "interactive".new-name
val nameInteractive = "interactive".new-name
val nameMain        = ".main".new-name
val nameCopy        = ".copy".new-name
val nameOpExpr      = ".opexpr".new-name

// Primitive operations
val nameIf          = "if".new-name
val nameCase        = "case".new-name

val nameTrace   = "trace".prelude-name
val nameLog     = "log".prelude-name
val namePhantom = "phantom".prelude-name


// Primitive constructors
val nameTpDelay          = "delay".prelude-name

val namePatternMatchError = "error-pattern".prelude-name
val nameMainConsole      = "main-console".prelude-name
val nameSubStr1          = "substr1".prelude-name
val nameDec              = "dec".prelude-name


val nameTpArray     = "std/data/array".new-name.qualify("array".new-name)
val nameVector      = "unvlist".prelude-name

val namesSameSize   = ["id","map","reverse","foldl","foldr"].map(prelude-name)

// Lists
val nameNull        = "Nil".prelude-name
val nameCons        = "Cons".prelude-name
val nameTpList      = "list".prelude-name

val nameIntConst    = ".int-const".prelude-name


val nameIntAdd      = "int-add".prelude-name
val nameIntSub      = "int-sub".prelude-name

// Primitive Type Constructors
val nameTpOperation = "operation".prelude-name
val nameTpHandlerBranch0 = "handler-branch0".prelude-name
val nameTpHandlerBranch1 = "handler-branch1".prelude-name

val nameTpValueOp   = "value".prelude-name

val nameAssert      = "assert".prelude-name

val nameTpCps       = "cps".prelude-name
val nameInCps       = "incps".prelude-name
val nameTpCont      = "cont".prelude-name

val nameTpAsync     = "std/async".new-name.qualify("async".new-name)
val nameTpAsyncX    = "std/async".new-name.qualify("asyncx".new-name)

fun name-yield-op(n:int): name
  prelude-name (".yieldop" ++ (if (n == 0) then "" else "-x" ++ n.show))

val nameToAny       = ".toany".prelude-name
val nameApplyK      = ".applyK".prelude-name
val nameIsValidK    = ".isValidK".prelude-name

fun name-make-handler(handlerSort: handlerSort, n: int): name
  prelude-name (".make" ++ (if (!handlerSort.is-handler-normal) then handlerSort.show else "") ++ "Handler" ++ n.show)

fun name-make-handler-ret(n: int): name
  prelude-name (".makeHandlerRet" ++ n.show)

fun name-make-context-tp(n: int): name
  prelude-name ("resume-context" ++ (if (n==0) then "" else "1"))

val nameMakeNull    = ".null-any".prelude-name
val nameConstNull   = "null-const".prelude-name
val nameReturnNull   = "null-return".prelude-name
val nameReturnNull1   = "null-return1".prelude-name

val nameLift        = "lift".prelude-name
val nameTpYld       = "yld".prelude-name
val nameInject      = ".inject-effect".prelude-name
val nameInjectExn   = "inject-exn".prelude-name
val nameInjectResource = ".inject-resource".prelude-name
val nameTpResourceTag = "resource-tag".prelude-name
val nameConResourceTag = ".Resource-tag".prelude-name

val nameTpOpMatch   = "opmatch".prelude-name
val nameOpMatch     = ".conOpMatch".prelude-name
val nameOpNoMatch   = ".conOpNoMatch".prelude-name

val nameConEv       = "Ev".prelude-name

val nameTpNull      = "null".prelude-name
val nameTpIO        = "io".prelude-name

val nameTpNamed     = "nmd".prelude-name
val nameTpScope     = "scope".prelude-name
val nameTpPartial   = "exn".prelude-name
val nameTpPure      = "pure".prelude-name

val nameTpException  = "exception".prelude-name

val nameTpMDict     = nameDict.qualify("mdict".new-name)
val nameTpDict      = nameDict.qualify("dict".new-name)
val nameTpBuilder   = ("std/text/string").new-name.qualify("builder".new-name)

fun cfield-name(n: string): name
  n.core-types-name()

val nameTpCCtxx    = "cctx".cfield-name
val nameTpCCtx      = "ctx".cfield-name
val nameCCtxCreate    = ".cctx-create".cfield-name
val nameCCtxHoleCreate      = ".cctx-hole-create".cfield-name
val nameCCtxExtend = ".cctx-extend".cfield-name
val nameCCtxComposeExtend = ".cctx-compose-extend".cfield-name
val nameCCtxEmpty = ".cctx-empty".cfield-name
val nameCCtxSetCtxPath = ".cctx-setcp".cfield-name
val nameCCtxApply = "([])".cfield-name
val nameCCtxCompose = "(++)".cfield-name
val nameTpFieldAddr = "field-addr".cfield-name
val nameFieldAddrOf = ".field-addr-of".cfield-name


// std/core/hnd
val nameTpHTag      = "htag".core-hnd-name

fun name-tp-clause(i:int): name
  ("clause" ++ i.show).core-hnd-name

val nameTpEv        = "ev".core-hnd-name
val nameTpEvv       = "evv".core-hnd-name
val nameTpEvIndex   = "ev-index".core-hnd-name

fun name-clause(sort, i: int): name
  ("clause-" ++ sort ++ i.show).core-hnd-name

val nameTpResumeContext = "resume-context".core-hnd-name

val nameHTag        = ".new-htag".core-hnd-name

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
// prelude-name  "bind"
val nameBind        = "yield-bind".core-hnd-name
val nameBind2       = "yield-bind2".core-hnd-name
val nameEffectOpen  =  "@open".core-types-name // prelude-name ".open"

val nameInitially   = "initially".core-hnd-name
val nameFinally     = "finally".core-hnd-name

fun name-clause-tail-no-op(n: n, ?show: (n) -> e string): e name
  core-hnd-name("clause-tail-noop" ++ show(n))

fun is-clause-tail-name(n: name): maybe<int>
  val s = n.nameId
  if s.starts-with("clause-tail").bool && s.list.drop(11).all(is-digit) then
    s.list.drop(11).string.parse-int()
  else
    Nothing

// std/core/types

val nameDecreasing  = "unsafe-decreasing".core-types-name
val nameUnsafeTotal = "unsafe-total".core-types-name

val nameAssigned    = "assigned".new-name
val nameIndex       = "[]".new-name
val nameAssign      = ":=".core-types-name
val nameRefSet      = "set".core-types-name
val nameLocalSet    = "local-set".core-types-name
val nameLocalGet    = "local-get".core-types-name
val nameDeref       = "!".core-types-name
val nameByref       = "byref".core-types-name

val namePredHeapDiv = "hdiv".core-types-name
val namePredEffDiv  = "ediv".core-types-name
val nameReturn      = ".return".core-types-name

val nameTpRef       = "ref".core-types-name
val nameTpLocalVar  = "local-var".core-types-name
val nameTpLocal     = "local".core-types-name
val nameRef         = "ref".core-types-name
val nameLocalNew    = "local-new".core-types-name
val nameLocal       = "local-var".core-hnd-name
val nameRunLocal    = "local-scope".core-types-name

val nameTpTotal     = "total".prelude-name
val nameTpDiv       = "div".core-types-name
val nameTpAlloc     = "alloc".core-types-name
val nameTpRead      = "read".core-types-name
val nameTpWrite     = "write".core-types-name
val nameTpST        = "st".core-types-name

val nameEffectEmpty = "<>".core-types-name
val nameEffectExtend= "<|>".core-types-name
val nameEffectAppend= ".<+>".new-name  // only used during kind inference

val nameAnd         = "&&".core-types-name
val nameOr          = "||".core-types-name

val nameTpHandled   = "handled".core-types-name
val nameTpHandled1  = "handled1".core-types-name

val nameIdentity    = "id".core-types-name

val nameByte        = "uint8".prelude-name
val nameInt8        = "int8".prelude-name
val nameInt16       = "int16".prelude-name
val nameInt32       = "int32".prelude-name
val nameInt64       = "int64".prelude-name
val nameSSizeT      = "ssize_t".prelude-name
val nameIntPtrT     = "intptr_t".prelude-name

val nameUnit        = "()".core-types-name
val nameTrue        = "True".core-types-name
val nameFalse       = "False".core-types-name

val nameJust        = "Just".core-types-name
val nameNothing     = "Nothing".core-types-name
val nameTpMaybe     = "maybe".core-types-name

val nameOptional    = "Optional".core-types-name
val nameOptionalNone= "None".core-types-name
val nameTpOptional  = "optional".core-types-name

val nameTpVoid      = "void".core-types-name
val nameTpUnit      = "()".core-types-name
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
val nameTpBox       = ".Box".core-types-name
val nameBoxCon      = ".Box".core-types-name
val nameBox         = ".box".core-types-name
val nameUnbox       = ".unbox".core-types-name

val nameTpReuse     = "reuse".core-types-name
val nameReuseNull   = "no-reuse".core-types-name
val nameDropReuse   = ".drop-reuse".core-types-name
val nameFreeReuse   = ".free-reuse".core-types-name
val nameAllocAt     = ".alloc-at".core-types-name
val nameAssignReuse = ".assign-reuse".core-types-name
val nameReuse       = ".reuse".core-types-name
val nameReuseIsValid= ".reuse-is-valid".core-types-name
val nameConFieldsAssign = ".con-fields-assign".core-types-name
val nameConTagFieldsAssign = ".con-tag-fields-assign".core-types-name
val nameKeep        = "keep".core-types-name
val nameSetTag      = ".set-tag".core-types-name

val nameDup         = ".dup".core-types-name
val nameDrop        = ".drop".core-types-name
val nameFree        = ".free".core-types-name
val nameDecRef      = ".dec-ref".core-types-name
val nameIsUnique    = ".is-unique".core-types-name
val nameKeepMatch   = ".keep-match".core-types-name
val nameDropMatch   = ".drop-match".core-types-name
val nameReuseMatch  = ".reuse-match".core-types-name

val nameReuseDrop   = ".reuse-drop".core-types-name

val nameDropSpecial    = ".drop-special".core-types-name

fun name-tuple(n: int): name
  core-types-name("(" ++ replicate(",", n - 1).join ++ ")")

fun is-name-tuple(n: name): bool
  val s = n.nameId.list
  n.nameModule == nameCoreTypes.nameId && s.length >= 2 && s.head.default(' ') == '(' && s.last.default(' ') == ')' && s.tail.init.all((fn(i) -> i == ','))

fun prelude-name(s: string): name
  nameSystemCore.qualify(s.new-name)

fun core-hnd-name(s: string): name
  nameCoreHnd.qualify(s.new-name)

fun core-types-name(s: string): name
  nameCoreTypes.qualify(s.new-name)

val nameSystemCore  = "std/core".new-name
val nameCoreHnd     = "std/core/hnd".new-name
val nameCoreTypes   = "std/core/types".new-name
val nameDict        = "std/data/dict".new-name

fun is-system-core-name(Name(m, _, _, _)): bool
  [nameSystemCore.nameId, nameCoreHnd.nameId, nameCoreTypes.nameId].any(fn(i) -> i == m)

fun is-primitive-name(Name(m, _, _, _)): bool
  [nameCoreHnd.nameId, nameCoreTypes.nameId].any(fn(i) -> i == m)

fun is-primitive-module(Name(_, _, m, _)): bool
  [nameCoreHnd.nameId, nameCoreTypes.nameId].any(fn(i) -> i == m)

// Primitive Kind Constructors
val nameKindStar    = "V".new-name
val nameKindLabel   = "X".new-name
val nameKindFun = "->".new-name
val nameKindPred    = "P".new-name
val nameKindEffect  = "E".new-name
val nameKindHeap    = "H".new-name
val nameKindScope   = "S".new-name
val nameKindHandled = "HX".new-name
val nameKindHandled1 = "HX1".new-name

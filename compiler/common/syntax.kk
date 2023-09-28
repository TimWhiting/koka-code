type jsTarget
  JsDefault
  JsNode
  JsWeb

type cTarget
  CDefault
  LibC
  Wasm
  WasmJs
  WasmWeb

value type target
  CS
  JS(t: jsTarget)
  C(t: cTarget)
  DefaultTarget

struct platform
  ptrSize: int // sizeof(intptr_t)
  sizeSize: int // sizeof(size_t)
  fieldSize: int // sizeof(kk_field_t) usually intptr_t but can be compressed
  headerSize: int // alignment calculation

val platform32 = Platform(4, 4, 4, 8)
val platform64 = Platform(8, 8, 8, 8)
val platform64c = Platform(8, 8, 4, 8) // Compressed
val platformJS = Platform(8, 4, 8, 0)
val platformCS = Platform(8, 4, 8, 0)

fun hasCompressedFields(p: platform): bool
  p.ptrSize != p.fieldSize

fun show(p: platform): string
  "Platform(ptrSize: {" ++ p.ptrSize.show ++ "}, sizeSize: {" ++ p.sizeSize.show ++ "}, fieldSize: {" ++ p.fieldSize.show ++ "}, headerSize: {" ++ p.headerSize.show ++ "})"

fun (==)(c1: cTarget, c2: cTarget): bool
  match (c1, c2)
    (CDefault, CDefault) -> True
    (LibC, LibC) -> True
    (Wasm, Wasm) -> True
    (WasmJs, WasmJs) -> True
    (WasmWeb, WasmWeb) -> True
    _ -> False

fun (==)(j1: jsTarget, j2: jsTarget): bool
  match (j1, j2)
    (JsDefault, JsDefault) -> True
    (JsNode, JsNode) -> True
    (JsWeb, JsWeb) -> True
    _ -> False

pub fun (==)(t1: target, t2: target): bool
  match (t1, t2)
    (CS, CS) -> True
    (JS(j1), JS(j2)) -> j1 == j2
    (C(c1), C(c2)) -> c1 == c2
    (DefaultTarget, DefaultTarget) -> True
    _ -> False

fun show(t: target): string
  match t
    CS -> "CS"
    JS(j) -> "JS(" ++ j.show ++ ")"
    C(c) -> "C(" ++ c.show ++ ")"
    DefaultTarget -> "Default"

fun show(t: jsTarget): string
  match t
    JsDefault -> "JsDefault"
    JsNode -> "JsNode"
    JsWeb -> "JsWeb"

fun show(t: cTarget): string
  match t
    CDefault -> "CDefault"
    LibC -> "LibC"
    Wasm -> "Wasm"
    WasmJs -> "WasmJs"
    WasmWeb -> "WasmWeb"

fun alignedSum(start: int, xs: list<int>): int
  xs.foldl(start, alignedAdd)

fun alignedAdd(x: int, y: int): int
  alignUp(x, y) + y

fun alignUp(x: int, y: int): int
  if y <= 0 then x
  else ((x + y - 1) / y) * y

type buildType
  DebugFull
  Debug
  RelWithDebInfo
  Release

fun show(b: buildType): string
  match b
    DebugFull -> "DebugFull"
    Debug -> "Debug"
    RelWithDebInfo -> "RelWithDebInfo"
    Release -> "Release"


// The flavour of a type variable. Types in a "Type.Assumption" (Gamma) and inferred types in "Core.Core"
// are always of the 'Bound' flavour. 'Meta' and 'Skolem' type variables only ever occur during type inference.
// Kind and Type variables come in three flavours: 'Unifiable'
// variables can be unified, 'Skolem's are non-unifiable (fresh)
// variables, and 'Bound' variables are bound by a quantifier.
type flavour
  Bound
  Skolem
  Meta // used for pretty printing

fun (==)(f1: flavour, f2: flavour): bool
  match (f1, f2)
    (Meta, Meta) -> True
    (Skolem, Skolem) -> True
    (Bound, Bound) -> True
    _ -> False

type visibility
  Public
  Private

fun (==)(v1: visibility, v2: visibility): bool
  match (v1, v2)
    (Public, Public) -> True
    (Private, Private) -> True
    _ -> False

fun show(v: visibility): string
  match v
    Public -> "Public"
    Private -> "Private"

type handlerSort
  HandlerNormal
  HandlerInstance

pub fun show(h: handlerSort): string
  match h
    HandlerNormal -> "HandlerNormal"
    HandlerInstance -> "HandlerInstance"

pub fun isHandlerInstance(h: handlerSort): bool
  match h
    HandlerInstance -> True
    HandlerNormal -> False

pub fun isHandlerNormal(h: handlerSort): bool
  match h
    HandlerInstance -> False
    HandlerNormal -> True

type operationSort
  OpVal
  OpFun
  OpExcept
  OpControlRaw
  OpControl
  OpControlErr

fun show(o: operationSort): string
  match o
    OpVal -> "OpVal"
    OpFun -> "OpFun"
    OpExcept -> "OpExcept"
    OpControlRaw -> "OpControlRaw"
    OpControl -> "OpControl"
    OpControlErr -> "OpControlErr"

type dataKind
  Inductive
  CoInductive
  Retractive

fun show(k: dataKind): string
  match k
    Inductive -> "Inductive"
    CoInductive -> "CoInductive"
    Retractive -> "Retractive"

value type dataDef
  DataDefValue(repr: valueRepr) // size in bytes and count of scannable fields
  DataDefNormal
  DataDefAuto
  DataDefRec
  DataDefOpen

fun show(d: dataDef): string
  match d
    DataDefValue(r) -> "DataDefValue(" ++ r.show ++ ")"
    DataDefNormal -> "DataDefNormal"
    DataDefAuto -> "DataDefAuto"
    DataDefRec -> "DataDefRec"
    DataDefOpen -> "DataDefOpen"

fun isRec(d: dataDef): bool
  match d
    DataDefRec -> True
    _ -> False
  
fun isOpen(d: dataDef): bool
  match d
    DataDefOpen -> True
    _ -> False
  
fun isValue(d: dataDef): bool
  match d
    DataDefValue -> True
    _ -> False

type valueRepr
  ValueRepr(pub rawSize: int, pub scanCount: int, pub alignment: int);

fun show(v: valueRepr): string
  "ValueRepr(rawSize: {" ++ v.rawSize.show ++ "}, scanCount: {" ++ v.scanCount.show ++ "}, alignment: {" ++ v.alignment.show ++ "})"

fun sizeScan(p: platform, v: valueRepr): (int, int)
  (p.size(v), v.scanCount)

fun size(p: platform, v: valueRepr): int
  v.rawSize + (v.scanCount * p.fieldSize)

fun isMixed(v: valueRepr): bool
  v.rawSize > 0 && v.scanCount > 0

fun isRaw(v: valueRepr): bool
  v.rawSize > 0 && v.scanCount == 0

pub val valueReprZero = ValueRepr(0,0,0)
fun valueReprRaw(m: int)
  ValueRepr(m,0,m)
fun valueReprScan(n: int)
  ValueRepr(0,n,0)

type defSort
  DefFun(param: list<paramInfo>, fipKind: fipT=noFip)
  DefVal
  DefVar

fun defFunEx(pinfos: list<paramInfo>, fipKind: fipT)
  if pinfos.all(fn(p) p.is-own) then DefFun([], fipKind) else DefFun(pinfos, fipKind)

fun defFun(pinfos: list<paramInfo>)
  defFunEx(pinfos, noFip)

fun show(s: defSort): string
  match s
    DefFun(p, f) -> "DefFun(" ++ p.show-list(show) ++ ", " ++ f.show ++ ")"
    DefVal -> "DefVal"
    DefVar -> "DefVar"

pub fun isFun(s: defSort): bool
  match s
    DefFun(_) -> True
    _ -> False

type paramInfo
  Borrow
  Own

fun (==)(p1: paramInfo, p2: paramInfo): bool
  match (p1, p2)
    (Borrow, Borrow) -> True
    (Own, Own) -> True
    _ -> False

fun show(p: paramInfo): string
  match p
    Borrow -> "Borrow"
    Own -> "Own"

type defInline
  InlineNever
  InlineAlways
  InlineAuto

fun show(i: defInline): string
  match i
    InlineNever -> "InlineNever"
    InlineAlways -> "InlineAlways"
    InlineAuto -> "InlineAuto"

type fixity
  FixInfix(prec: int, assoc: assoc)
  FixPrefix
  FixPostfix

fun show(f: fixity): string
  match f
    FixInfix(p, a) -> "FixInfix(" ++ p.show ++ ", " ++ a.show ++ ")"
    FixPrefix -> "FixPrefix"
    FixPostfix -> "FixPostfix"

type assoc
  AssocNone
  AssocRight
  AssocLeft

fun show(a: assoc): string
  match a
    AssocNone -> "AssocNone"
    AssocRight -> "AssocRight"
    AssocLeft -> "AssocLeft"

type fipT
  Fip(alloc: fipAlloc)
  Fbip(alloc: fipAlloc, tail: bool)
  NoFip(tail: bool)

fun show(f: fipT): string
  match f
    Fip(a) -> "Fip(" ++ a.show ++ ")"
    Fbip(a, t) -> "Fbip(" ++ a.show ++ ", " ++ t.show ++ ")"
    NoFip(t) -> "NoFip(" ++ t.show ++ ")"

value type fipAlloc
  AllocAtMost(i: int)
  AllocFinitely
  AllocUnlimited

fun show(a: fipAlloc): string
  match a
    AllocAtMost(0) -> "AllocAtMost(0)"
    AllocAtMost(n) -> "AllocAtMost(" ++ n.show ++ ")"
    AllocFinitely -> "AllocFinitely"
    AllocUnlimited -> "AllocUnlimited"

val noFip = NoFip(False)

fun isTail(f: fipT): bool
  match f
    Fip(_) -> True
    Fbip(_, t) -> t
    NoFip(t) -> t

fun alloc(f: fipT): fipAlloc
  match f
    Fip(a) -> a
    Fbip(a) -> a
    NoFip() -> AllocUnlimited

fun showFip(f: fipT)
  fun showTail(b: bool): string
    if b then "tail" else " "
  fun showN(n: fipAlloc): string
    match n
      AllocAtMost(0) -> ""
      AllocAtMost(n) -> "(" ++ n.show ++ ")"
      AllocFinitely -> "(n)"
      AllocUnlimited -> "" 
  match f
    Fip(n) -> "fip" ++ showN(n)
    Fbip(n, t) -> t.showTail ++ "fbip" ++ showN(n)
    NoFip(t) -> t.showTail
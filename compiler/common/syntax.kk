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

fun platform/(==)(p1: platform, p2: platform): bool
  p1.ptrSize == p2.ptrSize && p1.sizeSize == p2.sizeSize && p1.fieldSize == p2.fieldSize && p1.headerSize == p2.headerSize

fun hasCompressedFields(p: platform): bool
  p.ptrSize != p.fieldSize

fun platform/show(p: platform): string
  "Platform(ptrSize: {" ++ p.ptrSize.show ++ "}, sizeSize: {" ++ p.sizeSize.show ++ "}, fieldSize: {" ++ p.fieldSize.show ++ "}, headerSize: {" ++ p.headerSize.show ++ "})"

fun ctarget/(==)(c1: cTarget, c2: cTarget): bool
  match (c1, c2)
    (CDefault, CDefault) -> True
    (LibC, LibC) -> True
    (Wasm, Wasm) -> True
    (WasmJs, WasmJs) -> True
    (WasmWeb, WasmWeb) -> True
    _ -> False

fun jstarget/(==)(j1: jsTarget, j2: jsTarget): bool
  match (j1, j2)
    (JsDefault, JsDefault) -> True
    (JsNode, JsNode) -> True
    (JsWeb, JsWeb) -> True
    _ -> False

pub fun target/(==)(t1: target, t2: target): bool
  match (t1, t2)
    (CS, CS) -> True
    (JS(j1), JS(j2)) -> j1 == j2
    (C(c1), C(c2)) -> c1 == c2
    (DefaultTarget, DefaultTarget) -> True
    _ -> False

fun target/show(t: target): string
  match t
    CS -> "CS"
    JS(j) -> "JS(" ++ j.show ++ ")"
    C(c) -> "C(" ++ c.show ++ ")"
    DefaultTarget -> "Default"

fun jstarget/show(t: jsTarget): string
  match t
    JsDefault -> "JsDefault"
    JsNode -> "JsNode"
    JsWeb -> "JsWeb"

fun ctarget/show(t: cTarget): string
  match t
    CDefault -> "CDefault"
    LibC -> "LibC"
    Wasm -> "Wasm"
    WasmJs -> "WasmJs"
    WasmWeb -> "WasmWeb"

fun aligned/sum(start: int, xs: list<int>): int
  xs.foldl(start, aligned/add)

fun aligned/add(x: int, y: int): int
  align-up(x, y) + y

fun align-up(x: int, y: int): int
  if y <= 0 then x
  else ((x + y - 1) / y) * y

type buildType
  DebugFull
  Debug
  RelWithDebInfo
  Release

fun build-type/show(b: buildType): string
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

fun flavour/(==)(f1: flavour, f2: flavour): bool
  match (f1, f2)
    (Meta, Meta) -> True
    (Skolem, Skolem) -> True
    (Bound, Bound) -> True
    _ -> False

type visibility
  Public
  Private

fun visibility/(==)(v1: visibility, v2: visibility): bool
  match (v1, v2)
    (Public, Public) -> True
    (Private, Private) -> True
    _ -> False

fun visibility/show(v: visibility): string
  match v
    Public -> "Public"
    Private -> "Private"

type handlerSort
  HandlerNormal
  HandlerInstance

pub fun handler-sort/show(h: handlerSort): string
  match h
    HandlerNormal -> "HandlerNormal"
    HandlerInstance -> "HandlerInstance"

pub fun is-handler-instance(h: handlerSort): bool
  match h
    HandlerInstance -> True
    HandlerNormal -> False

pub fun is-handler-normal(h: handlerSort): bool
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

fun op-sort/show(o: operationSort): string
  match o
    OpVal -> "val"
    OpFun -> "fun"
    OpExcept -> "brk"
    OpControlRaw -> "rawctl"
    OpControl -> "ctl"
    OpControlErr -> ""

type dataKind
  Inductive
  CoInductive
  Retractive

fun datakind/show(k: dataKind): string
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

fun datadef/show(d: dataDef): string
  match d
    DataDefValue(r) -> "DataDefValue(" ++ r.show ++ ")"
    DataDefNormal -> "DataDefNormal"
    DataDefAuto -> "DataDefAuto"
    DataDefRec -> "DataDefRec"
    DataDefOpen -> "DataDefOpen"

fun datadef/is-rec(d: dataDef): bool
  d.is-dataDefRec
  
fun datadef/is-open(d: dataDef): bool
  d.is-dataDefOpen

fun datadef/is-value(d: dataDef): bool
  d.is-dataDefValue

type valueRepr
  ValueRepr(pub rawSize: int, pub scanCount: int, pub alignment: int);

fun valuerepr/show(v: valueRepr): string
  "ValueRepr(rawSize: {" ++ v.rawSize.show ++ "}, scanCount: {" ++ v.scanCount.show ++ "}, alignment: {" ++ v.alignment.show ++ "})"

fun scan/size(p: platform, v: valueRepr): (int, int)
  (p.size(v), v.scanCount)

fun full/size(p: platform, v: valueRepr): int
  v.rawSize + (v.scanCount * p.fieldSize)

fun is-mixed(v: valueRepr): bool
  v.rawSize > 0 && v.scanCount > 0

fun is-raw(v: valueRepr): bool
  v.rawSize > 0 && v.scanCount == 0

pub val valuerepr/zero = ValueRepr(0,0,0)
fun valueReprRaw(m: int)
  ValueRepr(m,0,m)
fun valueReprScan(n: int)
  ValueRepr(0,n,0)

type defSort
  DefFun(param: list<paramInfo>, fipKind: fipT=NoFip(False))
  DefVal
  DefVar

fun def-fun-ex(pinfos: list<paramInfo>, fipKind: fipT)
  if pinfos.all(fn(p) p.is-own) then DefFun([], fipKind) else DefFun(pinfos, fipKind)

fun def-fun(pinfos: list<paramInfo>)
  def-fun-ex(pinfos, no-fip)

fun defsort/show(s: defSort): string
  match s
    DefFun(p, f) -> "DefFun(" ++ p.show-list(show) ++ ", " ++ f.show ++ ")"
    DefVal -> "DefVal"
    DefVar -> "DefVar"

fun show-full(s: defSort): string
  match s
    DefFun(_, f) -> f.show ++ " fun"
    DefVal -> "val"
    DefVar -> "var"

pub fun defsort/is-fun(s: defSort): bool
  match s
    DefFun(_) -> True
    _ -> False

type paramInfo
  Borrow
  Own

fun param/(==)(p1: paramInfo, p2: paramInfo): bool
  match (p1, p2)
    (Borrow, Borrow) -> True
    (Own, Own) -> True
    _ -> False

fun param/show(p: paramInfo): string
  match p
    Borrow -> "Borrow"
    Own -> "Own"

type defInline
  InlineNever
  InlineAlways
  InlineAuto

fun definline/show(i: defInline): string
  match i
    InlineNever -> "InlineNever"
    InlineAlways -> "InlineAlways"
    InlineAuto -> "InlineAuto"

type fixity
  FixInfix(prec: int, assoc: assoc)
  FixPrefix
  FixPostfix

fun fixity/(==)(f1: fixity, f2: fixity): bool
  match (f1, f2)
    (FixInfix(p1, a1), FixInfix(p2, a2)) -> p1 == p2 && a1 == a2
    (FixPrefix, FixPrefix) -> True
    (FixPostfix, FixPostfix) -> True
    _ -> False

fun fixity/show(f: fixity): string
  match f
    FixInfix(p, a) -> "FixInfix(" ++ p.show ++ ", " ++ a.show ++ ")"
    FixPrefix -> "FixPrefix"
    FixPostfix -> "FixPostfix"

type assoc
  AssocNone
  AssocRight
  AssocLeft

fun assoc/(==)(a1: assoc, a2: assoc): bool
  match (a1, a2)
    (AssocNone, AssocNone) -> True
    (AssocRight, AssocRight) -> True
    (AssocLeft, AssocLeft) -> True
    _ -> False

fun assoc/show(a: assoc): string
  match a
    AssocNone -> "AssocNone"
    AssocRight -> "AssocRight"
    AssocLeft -> "AssocLeft"

type fipT
  Fip(alloc: fipAlloc)
  Fbip(alloc: fipAlloc, tail: bool)
  NoFip(tail: bool)

fun fipt/show(f: fipT): string
  match f
    Fip(a) -> "Fip(" ++ a.show ++ ")"
    Fbip(a, t) -> "Fbip(" ++ a.show ++ ", " ++ t.show ++ ")"
    NoFip(t) -> "NoFip(" ++ t.show ++ ")"

value type fipAlloc
  AllocAtMost(i: int)
  AllocFinitely
  AllocUnlimited

fun fipalloc/show(a: fipAlloc): string
  match a
    AllocAtMost(0) -> "AllocAtMost(0)"
    AllocAtMost(n) -> "AllocAtMost(" ++ n.show ++ ")"
    AllocFinitely -> "AllocFinitely"
    AllocUnlimited -> "AllocUnlimited"

pub val no-fip = NoFip(False)

fun fipt/is-tail(f: fipT): bool
  match f
    Fip(_) -> True
    Fbip(_, t) -> t
    NoFip(t) -> t

fun alloc(f: fipT): fipAlloc
  match f
    Fip(a) -> a
    Fbip(a) -> a
    NoFip() -> AllocUnlimited

fun show-fip(f: fipT)
  fun show-tail(b: bool): string
    if b then "tail" else " "
  fun show-n(n: fipAlloc): string
    match n
      AllocAtMost(0) -> ""
      AllocAtMost(n) -> "(" ++ n.show ++ ")"
      AllocFinitely -> "(n)"
      AllocUnlimited -> "" 
  match f
    Fip(n) -> "fip" ++ show-n(n)
    Fbip(n, t) -> t.show-tail ++ "fbip" ++ show-n(n)
    NoFip(t) -> t.show-tail
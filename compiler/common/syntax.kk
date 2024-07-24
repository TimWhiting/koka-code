//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 7/23/24: Commit bc34c8e

type jsTarget
  JsDefault
  JsNode
  JsWeb

fun jstarget/(==)(j1: jsTarget, j2: jsTarget): bool
  match (j1, j2)
    (JsDefault, JsDefault) -> True
    (JsNode, JsNode) -> True
    (JsWeb, JsWeb) -> True
    _ -> False

type cTarget
  CDefault
  LibC
  Wasm
  WasmJs
  WasmWeb

fun ctarget/(==)(c1: cTarget, c2: cTarget): bool
  match (c1, c2)
    (CDefault, CDefault) -> True
    (LibC, LibC) -> True
    (Wasm, Wasm) -> True
    (WasmJs, WasmJs) -> True
    (WasmWeb, WasmWeb) -> True
    _ -> False

value type target
  CS
  JS(t: jsTarget)
  C(t: cTarget)
  DefaultTarget

fun target/(==)(t1: target, t2: target): bool
  match (t1, t2)
    (CS, CS) -> True
    (JS(j1), JS(j2)) -> j1 == j2
    (C(c1), C(c2)) -> c1 == c2
    (DefaultTarget, DefaultTarget) -> True
    _ -> False

fun is-target-wasm(t: target): bool
  match t
    C(Wasm) -> True
    C(WasmJs) -> True
    C(WasmWeb) -> True
    _ -> False

fun target/show(t: target): string
  match t
    CS -> "cs"
    JS(JsWeb) -> "jsweb"
    JS(JsNode) -> "jsnode"
    JS -> "js"
    C(Wasm) -> "wasm"
    C(WasmJs) -> "wasmjs"
    C(WasmWeb) -> "wasmweb"
    C(LibC) -> "libc"
    C -> "c"
    DefaultTarget -> ""

struct platform
  ptrSize: int // sizeof(intptr_t)
  sizeSize: int // sizeof(size_t)
  fieldSize: int // sizeof(kk_field_t) usually intptr_t but may be smaller for compression
  headerSize: int // used for correct alignment calculation

val platform32 = Platform(4, 4, 4, 8)
val platform64 = Platform(8, 8, 8, 8)
val platform64c = Platform(8, 8, 4, 8) // Compressed fields
val platformJS = Platform(8, 4, 8, 0)
val platformCS = Platform(8, 4, 8, 0)

fun platform/(==)(p1: platform, p2: platform): bool
  p1.ptrSize == p2.ptrSize && p1.sizeSize == p2.sizeSize && p1.fieldSize == p2.fieldSize && p1.headerSize == p2.headerSize

fun has-compressed-fields(p: platform): bool
  p.ptrSize != p.fieldSize

fun platform/show(p: platform): string
  "Platform(sizeof(void*)=" ++ p.ptrSize.show ++ ", sizeof(size_t)=" ++ p.sizeSize.show ++ ", sizeof(kk_box_t)=" ++ p.fieldSize.show ++ ", sizeof(kk_header_t)=" ++ p.headerSize.show ++ ")"

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
    DebugFull -> "debugfull"
    Debug -> "debug"
    RelWithDebInfo -> "drelease"
    Release -> "release"

// Visibility

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
    HandlerNormal -> "normal"
    HandlerInstance -> "named"

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
    OpExcept -> "final ctl"
    OpControl -> "ctl"
    OpControlRaw -> "rawctl"
    OpControlErr -> ""

fun op-sort/string(o: operationSort): string
  match o
    OpVal -> "val"
    OpFun -> "fun"
    OpExcept -> "brk"
    OpControl -> "ctl"
    OpControlRaw -> "rawctl"
    OpControlErr -> ""

fun read-op-sort(s: string): maybe<operationSort>
  match s
    "val" -> Just(OpVal)
    "fun" -> Just(OpFun)
    "brk" -> Just(OpExcept)
    "ctl" -> Just(OpControl)
    "rawctl" -> Just(OpControlRaw)
    // legacy
    "except" -> Just(OpExcept)
    "control" -> Just(OpControl)
    "rcontrol" -> Just(OpControlRaw)
    _ -> Nothing

value type dataEffect
  DataNoEffect
  DataEffect(is-named: bool, is-linear: bool)

// DataKind

type dataKind
  Inductive
  CoInductive
  Retractive

fun datakind/show(k: dataKind): string
  match k
    Inductive -> "type"
    CoInductive -> "cotype"
    Retractive -> "rectype"

value type dataDef
  DataDefValue(repr: valueRepr) // value type
  DataDefNormal // reference type
  DataDefEffect(is-linear: bool, is-named: bool) // effect types
  DataDefRec
  DataDefOpen
  DataDefAuto // value or normal; determined by kind inference

fun datadef/(==)(d1: dataDef, d2: dataDef): bool
  match (d1, d2)
    (DataDefValue(r1), DataDefValue(r2)) -> r1 == r2
    (DataDefNormal, DataDefNormal) -> True
    (DataDefEffect(l1, n1), DataDefEffect(l2, n2)) -> l1 == l2 && n1 == n2
    (DataDefRec, DataDefRec) -> True
    (DataDefOpen, DataDefOpen) -> True
    (DataDefAuto, DataDefAuto) -> True
    _ -> False

fun datadef/show(d: dataDef): string
  match d
    DataDefValue(r) -> "val" ++ r.show
    DataDefNormal -> "normal"
    DataDefEffect(l, n) -> (if l then "linear " else "") ++ (if n then "named " else "") ++ "effect"
    DataDefRec -> "rec"
    DataDefOpen -> "open"
    DataDefAuto -> "auto"

fun datadef/is-rec(d: dataDef): bool
  match d
    DataDefValue -> False
    DataDefNormal -> False
    DataDefAuto -> False
    _ -> True
  
fun datadef/is-open(d: dataDef): bool
  d.is-dataDefOpen

fun datadef/is-value(d: dataDef): bool
  d.is-dataDefValue

fun datadef/is-normal(d: dataDef): bool
  d.is-dataDefNormal

fun datadef/size(d: dataDef, p: platform): int
  match d
    DataDefValue(r) -> size(p, r)
    _ -> p.fieldSize

value struct valueRepr
  rawSize: int // size in bytes
  scanCount: int // count of scannable fields 
  alignment: int // minimal alignment

fun valuerepr/show(v: valueRepr): string
  "{" ++ v.rawSize.show ++ ", " ++ v.scanCount.show ++ ", " ++ v.alignment.show ++ "}"

fun scan-size(p: platform, v: valueRepr): (int, int)
  (p.size(v), v.scanCount)

fun valuerepr/size(p: platform, v: valueRepr): int
  v.rawSize + (v.scanCount * p.fieldSize)

fun is-mixed(v: valueRepr): bool
  v.rawSize > 0 && v.scanCount > 0

fun is-raw(v: valueRepr): bool
  v.rawSize > 0 && v.scanCount == 0

pub val valuerepr/zero = ValueRepr(0,0,0)

fun value-repr-raw(m: int)
  ValueRepr(m,0,m)

fun value-repr-scan(n: int)
  ValueRepr(0,n,0)

type defSort
  DefFun(param: list<paramInfo>, fipKind: fipT=NoFip(False))
  DefVal
  DefVar

type paramInfo
  Borrow
  Own

fun def-fun-ex(pinfos: list<paramInfo>, fipKind: fipT)
  if pinfos.all(fn(p) p.is-own) then DefFun([], fipKind) else DefFun(pinfos, fipKind)

fun def-fun(pinfos: list<paramInfo>)
  def-fun-ex(pinfos, no-fip)

fun defsort/show(s: defSort): string
  match s
    DefFun(p, f) -> "fun"
    DefVal -> "val"
    DefVar -> "var"

fun show-full(s: defSort): string
  match s
    DefFun(_, f) -> f.show ++ " fun"
    DefVal -> "val"
    DefVar -> "var"

pub fun defsort/is-fun(s: defSort): bool
  match s
    DefFun(_) -> True
    _ -> False

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
    InlineNever -> "noinline"
    InlineAlways -> "inline"
    InlineAuto -> "autoinline"

// Fixities

// Operator fixity
type fixity
  FixInfix(prec: int, assoc: assoc) // Precedence and associativity
  FixPrefix
  FixPostfix

// Operator associativity
type assoc
  AssocNone
  AssocRight
  AssocLeft

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

// Fip

type fipT
  Fip(alloc: fipAlloc)
  Fbip(alloc: fipAlloc, tail: bool)
  NoFip(tail: bool)

fun fipt/show(f: fipT): string
  match f
    Fip(a) -> "fip(" ++ a.show ++ ")"
    Fbip(a, t) -> "fbip(" ++ a.show ++ ", " ++ t.show ++ ")"
    NoFip(t) -> "NoFip(" ++ t.show ++ ")"

value type fipAlloc
  AllocAtMost(i: int)
  AllocFinitely
  AllocUnlimited

fun fipa/cmp(f1: fipAlloc, f2: fipAlloc)
  match (f1, f2)
    (AllocAtMost(n1), AllocAtMost(n2)) -> n1.cmp(n2)
    (_, AllocAtMost) -> Gt
    (AllocAtMost(n), AllocFinitely) -> Lt
    (AllocFinitely, AllocFinitely) -> Eq
    (AllocUnlimited, AllocFinitely) -> Gt
    (AllocUnlimited, AllocUnlimited) -> Eq
    (_, AllocUnlimited) -> Lt

fun combine(f1: fipAlloc, f2: fipAlloc)
  match (f1, f2)
    (AllocAtMost(n), AllocAtMost(m)) -> AllocAtMost(n + m)
    _ -> AllocFinitely

val fipa/zero = AllocAtMost(0)

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
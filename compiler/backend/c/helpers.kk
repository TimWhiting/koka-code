import compiler/core/core
import compiler/common/syntax
import compiler/common/failure
import compiler/common/name
import compiler/common/nice
import compiler/common/name-prim
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
import compiler/common/color-scheme
import std/os/path

alias asmEff = <pure,asm,compFlags,uniquePhase,colorSchemeEffect,newtypesEff,printer,subst,documentation,niceEff<typeVar>,ppEnvEff,precEff,prettyTypeEff>

// Put the things that need overriding in here
effect subst
  val substEnv: list<(tName, doc)> // substituting names
  val cdefName: name // current definition
  val cdefToHeader: bool // emit current def to header?

effect asm
  fun emitToH(d: doc): ()
  fun emitToC(d: doc): ()
  fun emitToInit(d: doc): ()
  fun emitToTop(d: doc): ()
  fun emitToDone(d: doc): ()
  fun getInit(): doc
  fun getDone(): doc
  fun getTop(): doc
  fun addCanonical(lam: canonicalLambda): bool // true if first instance, otherwise false
  // TODO: Canonical lambda
  val modName: name // current module
  val prettyModName: doc // pretty printed module name
  // TODO: Pretty.Env
  val targetPlatform: platform
  val eagerPatBind: bool
  val enableReuse: bool
  val enableSpecialize: bool
  val enableReuseSpecialize: bool
  val enableBorrowInference: bool
  val cTarget: cTarget
  val borrowed: borrowed
  val stackSize: int
  val buildType: buildType
  val sourceDir: path
  val debug: bool;

value struct canonicalLambda
  canonicalName : name
  fieldNames: list<(name, bool)>

fun (==)(fn1: list<(name, bool)>, fn2: list<(name, bool)>): bool
  match (fn1, fn2)
    (Cons((n1, b1), r1), Cons((n2, b2), r2)) -> n1 == n2 && b1 == b2 && r1.unsafe-decreasing == r2 
    _ -> False

fun (==)(c1: canonicalLambda, c2: canonicalLambda): pure bool
  c1.canonicalName == c2.canonicalName && c1.fieldNames == c2.fieldNames

fun show(c: canonicalLambda): string
  c.canonicalName.show ++ "(" ++ c.fieldNames.map(fn(n) n.fst.show ++ " " ++ n.snd.show).join(", ") ++ ")"

// Effect helpers
fun emitToCurrentDef(d: doc)
  if cdefToHeader then emitToH(d)
  else emitToC(d)

fun setNameSubstitutions(subs, f)
  with override
    val substEnv = subs
    val cdefName = cdefName
    val cdefToHeader = cdefToHeader
  f()

fun setDef(d: name, toHeader: bool, f)
  with override
    val substEnv = substEnv
    val cdefName = d
    val cdefToHeader = toHeader
  f()

fun localUnique(f)
  val u = updateUnique(id)
  val x = f()
  setUnique(u)
  x

fun newVarName(s: string): asmEff name
  newName("." ++ s ++ newUnique().show)

fun newVarNames(i: int): asmEff list<name>
  Cons(newVarName("x"), newVarNames(i - 1))

fun newDefVarName(s: string)
  postpend("-" ++ s ++ newUnique().show, cdefName)

fun newCanonicalVarName(s: string)
  postpend("-" ++ s, modName)

fun conName(e: expr)
  unsafe-no-div
    try({match e {Con(tn) -> tn}}) fn(_)
      trace("Failed in top level extracting con name of " ++ e.show)
      TName("error".newName, typeAny)

fun getFormat(tname: tName, formats: list<(target, string)>)
  match formats.find(fn((t, _)) t == C(cTarget))
    Nothing -> 
      trace("warning: C backend does not support external in " ++ tname.show)
      "kk_unsuported_external(\"" ++ tname.show ++ "\")"
    Just(x) -> x.snd

fun genDefName(tname: tName)
  tname.getName.unqualify.cppName

fun genVarName(s: string)
  newVarName(s).cppName

fun genVarNames(i: int)
  newVarNames(i).map(cppName)

fun genCommentTName(tname: tName)
  tname.getName.cppName |+| comment(tname.tNameType.ppType)

// Classification
fun maxScanCountOf(l: list<(conInfo, conRepr, list<(name,ktype)>, int)>): int
  l.foldl(0, fn(m, (_, _, _, sc)) if sc > m then sc else m)

fun minScanCountOf(l: list<(conInfo, conRepr, list<(name,ktype)>, int)>): int
  l.foldl(l.maxScanCountOf, fn(m, (_, _, _, sc)) if sc < m then sc else m)

fun dataReprMayHaveSingletons(d: dataRepr): bool
  match d
    DataAsMaybe -> True
    DataAsList -> True
    DataSingleNormal -> True
    DataSingle(hasSingletons) -> hasSingletons
    DataNormal(hasSingletons) -> hasSingletons
    _ -> False

fun patternVarFree(p)
  p.is-patWild

fun isPat(q: pattern, b: bool): bool
  match q
    PatWild -> False
    PatLit -> False
    PatVar(_, q') -> q'.isPat(b)
    PatCon(tn) -> tn.getName == (if b then nameTrue else nameFalse)

fun extractExternal(e: expr): asmEff maybe<(tName, string, list<expr>)>
  fun format(tn:tName, fs:list<(target,string)>)
    match lookupTarget(C(cTarget), fs)
      Nothing -> fail("backend does not support external in " ++ tn.show ++ fs.show-list(fn((t,s)) t.show ++ ":" ++ s))
      Just(f) -> f
  match e
    App(TypeApp(Var(tname, InfoExternal(formats)), _), args) ->
      Just((tname, tname.format(formats), args))
    App(Var(tname, InfoExternal(formats)), args) ->
      Just((tname, tname.format(formats), args))
    _ -> Nothing

fun isFunExpr(e: expr): bool
  match e
    TypeApp(e) -> isFunExpr(e)
    TypeLam(_, e) -> isFunExpr(e)
    Lam -> True
    _ -> False

fun isReuseNull(e: expr)
  match e
    App(Var(v, InfoExternal), []) -> v.getName == nameReuseNull
    _ -> False

fun isInlineableExpr(ex: expr): pure bool
  match ex
    TypeApp(e) -> e.isInlineableExpr
    TypeLam(_, e) -> e.isInlineableExpr
    ELit(LitString) -> False
    // C has no guarantee on argument evaluation so we only allow a select few operations to be inlined
    App(Var(v, InfoExternal), []) -> 
      val n = v.getName
      [nameYielding,nameReuseNull,nameCCtxHoleCreate].any(fn(n') n == n')
    // App (Var v (InfoExternal _)) [arg] | getName v `elem` [nameBox,nameDup,nameInt32] -> isInlineableExpr arg
    App(Var(v), [arg]) | [nameBox,nameInt32,nameReuse,nameReuseIsValid,nameIsUnique].any(fn(n') n' == v.getName) ->
      arg.isInlineableExpr
    // App (Var v (InfoExternal _)) args -> hasTotalEffect (typeOf v) &&  all isPureExpr args  -- yielding() etc.

    // App (Var v _) [arg] | getName v `elem` [nameBox,nameUnbox] -> isInlineableExpr arg
    //
    // TODO: comment out for now as it may prevent a tailcall if inlined
    // App f args       -> -- trace ("isInlineable f: " ++ show f) $
    //                      isPureExpr f && all isPureExpr args
    //                      -- all isInlineableExpr (f:args)
    //                      && not (isFunExpr f) -- avoid `fun() {}(a,b,c)` !
    //                      -- && getParamArityExpr f == length args
    _ -> ex.isPureExpr

fun isPureExpr(ex: expr): pure bool
  match ex
    TypeApp(e) -> e.isPureExpr
    TypeLam(_, e) -> e.isPureExpr
    Var(_, InfoExternal) -> False
    Var -> True
    Con -> ex.typeOf.splitFunScheme.is-nothing
    ELit(LitString) -> False // for our purposes, it's not pure (as it needs a declaration)
    ELit -> True
    Lam -> True
    _ -> False   

fun isTailCalling(ex: expr, n: name): bool
  fun f2(g: guard)
    g.body.unsafe-decreasing.isTailCalling(n) // does the guarded expression tailcall?
  fun f1(b: branch)
    b.guards.any(f2) // does any of the guards tailcall?
  match ex
    TypeApp(e) -> isTailCalling(e.unsafe-decreasing, n) // trivial
    TypeLam(_, e) -> isTailCalling(e.unsafe-decreasing, n) // trivial
    Lam -> False // lambda body is a new context, can't tailcall
    Var -> False // variable is not a call
    Con -> False // constructor is not a call
    ELit -> False // literal is not a call
    App(Var(tn, info), args) | tn.getName == n -> info.arity == args.length // direct application can be a tail call
    App(TypeApp(Var(tn, info)), args) | tn.getName == n -> info.arity == args.length // polymorphic direct application can be a tail call
    App(Var(tn), [e]) | tn.getName == nameReturn -> e.isTailCalling(n) // return is transparent in terms of tail calling
    App -> False
    Let(_, e) -> e.unsafe-decreasing.isTailCalling(n) // tail calls can only happen in the actual body
    Case(_, bs) -> bs.any(f1)

type result
  ResultReturn(tn: maybe<tName>, args: list<tName>) // first field carries function name if not anonymous and second the arguments which are always known
  ResultAssign(tn: tName, label: maybe<name>) // variable name nad optional label to break

// Pretty printing

type cType
  CBox
  CFun(args: list<cType>, res: cType)
  CData(nm: name)
  CPrim(prim: string)

fun cType(tp: ktype): cType
  match tp
    TForAll(_, _, t) -> t.cType
    TFun(pars, _, res) -> CFun(pars.map(fn(p) p.snd.unsafe-decreasing.cType), res.cType)
    TApp(t) -> t.cType
    TCon(c) -> c.cTypeCon
    TVar -> CBox
    TSyn(_, _, t) -> t.cType

fun cTypeCon(tp: typeCon): cType
  val nm = tp.name
  if nm == nameTpInt then CPrim("kk_integer_t")
  elif nm == nameTpString then CPrim("kk_string_t")
  elif nm == nameTpVector then CPrim("kk_vector_t")
  elif nm == nameTpEvv then CPrim("kk_evv_t")
  elif nm == nameTpChar then CPrim("kk_char_t") // 32-bit unicode point
  elif nm == nameTpSSizeT then CPrim("kk_ssize_t")
  elif nm == nameTpIntPtrT then CPrim("intptr_t")
  elif nm == nameTpFloat then CPrim("double")
  elif nm == nameTpBool then CPrim("bool")
  elif nm == nameTpUnit then CPrim("kk_unit_t")
  elif nm == nameTpInt64 then CPrim("int64_t")
  elif nm == nameTpInt8 then CPrim("int8_t")
  elif nm == nameTpInt16 then CPrim("int16_t")
  elif nm == nameTpInt32 then CPrim("int32_t")
  elif nm == nameTpFloat32 then CPrim("float")
  elif nm == nameTpFloat16 then CPrim("float") // float16 is only used for storage
  elif nm == nameTpRef || nm == nameTpLocalVar then CPrim("kk_ref_t")
  elif nm == nameTpBox || nm == nameTpAny then CPrim("kk_box_t")
  elif nm == nameTpReuse then CPrim("kk_reuse_t")
  elif nm == nameTpFieldAddr then CPrim("kk_field_addr_t")
  else CData(nm.typeClassName)

fun typeClassName(n: name)
  prepend(".", n)

fun cppVis(v: visibility): doc
  empty

fun typeConClassName(n: name)
  n

fun cPrimCanBeBoxed(s: string): bool
  ["kk_char_t", "int64_t", "int16_t", "int32_t", "float", "double", "intptr_t", "kk_ssize_t"].any(fn(x) x == s)

fun cppType(tp: ktype): doc
  match tp.cType
    CBox -> "kk_box_t".text
    CFun -> "kk_function_t".text
    CData(nm) -> cppName(nm)
    CPrim(prim) -> prim.text

fun ppVarDecl(TName(nm, tp): tName): doc
  tp.cppType |+| nm.cppName

fun ppDefName(n: name)
  cppName(n.unqualify)

val contextDoc = "_ctx".text
val contextParam = "kk_context_t* _ctx".text

val emptyArgs = arguments([])
val emptyParams = parameters([])

fun parameters(pars: list<doc>): doc
  tupled(pars ++ [contextParam])

fun arguments(args: list<doc>): doc
  tupled(args ++ [contextDoc])

fun ppLit(l: lit): <exn,compFlags> doc
  match l
    LitInt(i) ->
      if i.isSmallInt then text("kk_integer_from_small") |.| parens(i.pretty)
      elif i.isSmallInt32 then text("kk_integer_from_int") |.| arguments([i.pretty])
      else "kk_integer_from_string".text |.| arguments([dquotes(i.pretty)])
    LitChar(c) ->
      val c' = c.head-char.unjust
      if c' >= ' ' && c' <= '~' then c.show.text
      else c'.int.show-hex(4).text
    LitFloat(d) -> d.show.text
    LitString(s) -> fail("backend/c/from-core: ppLit: cannot inline string literal: " ++ s.show)

fun cString(s: string)
  fun bytes(bs: list<int>)
    ("\" \"" ++ bs.map(fn(b) b.show-hex(2, pre="\\x")).join ++ "\" \"").text
  fun escape(c: char): (doc, int)
    if c.int == 0 then (bytes([0xC0, 0x80]), 2) // embedded zero character
    elif c < ' ' then
      (if c == '\n' then "\\n".text
      elif c == '\t' then "\\t".text
      elif c == '\r' then "\\r".text
      else bytes([c.int]), 1)
    elif c <= '\x7F' then
      (if c == '\"' then "\\\"".text
      elif c == '\\' then "\\\\".text
      elif c == '?' then "\\?".text // avoid accidental trigraphs
      else c.char, 1)
      // TODO: BIG UTF-8
    else ("".text, 0)
  val (cstr, ccnt) = s.list.map(escape).unzip
  (dquotes(cstr.hcat), ccnt.sum)

fun genLitInt32(i: int)
  if i == minSmallInt32 then parens("INT32_MIN".text)
  else parens("KK_I32".text |.| parens(i.pretty))

fun genLitInt64(i: int)
  if i == minSmallInt64 then parens("INT64_MIN".text)
  else parens("KK_I64".text |.| parens(i.pretty))

fun genLitUint8(i: int)
  parens("(uint8_t)".text |.| parens(i.pretty))

fun genLitSSizeT(i: int)
  parens("KK_IZ".text |.| parens(i.pretty))

fun genLitIntPtrT(i: int)
  parens("KK_IP".text |.| parens(i.pretty))

fun isSmallLitInt(e)
  match e
    ELit(LitInt(i)) -> isSmallInt(i)
    _ -> False

fun isSmallInt(i)
  i >= minSmallInt && i < maxSmallInt
val maxSmallInt = 8191 // 2^13 -1 (conservative 14 bits on 32-bits platform)
val minSmallInt = -8192

fun isSmallInt32(i)
  i >= minSmallInt32 && i < maxSmallInt32
val minSmallInt32 = -2147483648
val maxSmallInt32 = 2147483647

fun isSmallInt64(i)
  i >= minSmallInt64 && i < maxSmallInt64
val minSmallInt64 = -9223372036854775808
val maxSmallInt64 = 9223372036854775807

fun isSmallUInt8(i)
  i >= 0 && i < 255

fun isSmallSSizeT(i)
  match targetPlatform.ptrSize
    4 -> i > minSmallInt32 && i < maxSmallInt32
    8 -> i > minSmallInt64 && i < maxSmallInt64
    _ -> fail("backend/c/from-core: isSmallSSizeT: unknown platform ssize_t: " ++ targetPlatform.show)

fun isSmallIntPtrT(i)
  match targetPlatform.ptrSize
    4 -> i > minSmallInt32 && i < maxSmallInt32
    8 -> i > minSmallInt64 && i < maxSmallInt64
    _ -> fail("backend/c/from-core: isSmallIntPtrT: unknown platform intptr_t: " ++ targetPlatform.show)

fun cppName(n: name): doc
  if n.isQualified then ppModName(n.qualifier) |.| "_".text |.| n.unqualify.show.asciiEncode(False).text
  else n.encode(False)

fun ppQName(modName: name, name: name): doc
  if modName == name.qualifier then cppName(name.unqualify)
  else cppName(name)

fun ppModName(n: name): doc
  "kk_".text |.| n.encode(True)

fun encode(n: name, isModule: bool)
  val s = n.show.asciiEncode(isModule)
  if s.isReserved || s == "" || s.head-char.map(is-digit).default(False) then ("kkloc_" ++ s).text
  else s.text

fun isReserved(s: string): bool
  if s.starts-with("kk_").is-just then True
  else reserved.any(fn(r) r == s)

val reserved = [ 
  // C pseudo-keywords
  "bool", "toString", "arguments", "eval",
  // C types
  "char", "int", "intptr_t", "long", "short", "signed", "size_t",
  "ssize_t", "intptr_t", "uintptr_t", "unsigned", "uint8_t",
  // C keywords
  "async", "await", "break", "case", "catch", "continue", "const", "debugger",
  "default", "delete", "do", "else", "finally", "for", "function", "if", "in",
  "instanceof", "new", "return", "register", "switch", "this", "throw", "try", "typeof",
  "var", "void", "while", "with", "yield",
  // reserved for future use
  "class", "enum", "export", "extends", "import", "super",
  // special macros
  "errno", "exception_info"
]

fun ppConField(n: name, t: ktype): doc
  t.cppType |+| n.unqualify.cppName |.| semi

fun conTestName(c: conInfo): doc
  cppName(makeHiddenName("is", c.name))

fun conTestNameX(nm: name): doc
  cppName(makeHiddenName("is", nm))

fun conTagName(c: conInfo): doc
  cppName(makeHiddenName("tag", c.name))

fun primName(prim: string, d: doc)
  if prim == "" then d else
    d |.| "_".text |.| prim.text

fun primNameType(prim: string, s: string)
  val start = if s.starts-with("kk_").is-just then "" else "kk_"
  val end = match s.ends-with("_t") { Just(x) -> x.string; _ -> s}  
  primName(prim, (start ++ end).text)

fun conBaseCastName(c: conInfo): doc
  cppName(makeHiddenName("base", c.name))

fun conBaseCastNameX(c: name): doc
  cppName(makeHiddenName("base", c))

fun conCreateName(c: conInfo): doc
  makeHiddenName("new", c.name).cppName

fun conCreateNameX(c: name): doc
  makeHiddenName("new", c).cppName

fun conSingletonName(c: conInfo): doc
  makeHiddenName("singleton", c.name).cppName

fun conAsName(c: conInfo): doc
  cppName(makeHiddenName("as", c.name))

fun conAsNameX(c: name): doc
  cppName(makeHiddenName("as", c))

fun openTagName(n: name): doc
  cppName(makeHiddenName("tag", n))

fun ntParameters(pars: list<(name, ktype)>): doc
  parameters(pars.map(fn((n, t)) t.cppType |+| n.unqualify.cppName))

fun closFnParameters(pars: list<(name, ktype)>): doc
  parameters(Cons("void* fnPtr".text, pars.map(fn((n, t)) t.cppType |+| n.unqualify.cppName)))

fun vcatBreak(l: list<doc>): doc
  linebreak |.| l.vcat

fun parensIf(d: doc) // avoid parens if already parenthesized
  if d.dStartsWith("(") && d.dEndsWith(")") || d.dStartsWith("kk_likely") then d
  else parens(d)

fun inlineblock(d: doc)
  if d.dStartsWith("{") then d
  else hang("{".text |+| d, 2) |--| "}".text

fun block(d: doc)
  if d.dStartsWith("{") then d
  else "{".text |--| tab(d) |--| "}".text

fun block1(l: list<doc>)
  match l
    [d] -> "{".text |+| d |+| "}".text
    _ -> block(l.vcat)

fun tblock(tp: doc, d: doc)
  "{".text |+| tp |--| tab(d) |--| "}".text

fun tcoBlock(tp: doc, d: doc)
  tblock(tp, "kk__tailcall: ;".text |--| d)

val tailcall = "goto kk__tailcall;".text

fun object(xs: list<(doc, doc)>): doc
  "{".text |+| hcat(xs.map(fn((d1, d2)) d1 |.| colon |+| d2).punctuate(comma |.| space)) |+| "}".text

fun tab(d: doc)
  indent(d, 2)

val typeComment = comment

fun comment(d: doc)
  "/*".text |+| d |+| "*/".text

fun linecomment(d: doc)
  "//".text |+| d

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

fun debugComment(s: string)
  if debug then comment(s.text)
  else pprint/Empty

fun debugWrap(d: doc, s: string)
  if debug then debugComment("<" ++ s ++ ">") |--| tab(d) |--| debugComment("</" ++ s ++ ">")
  else d

val tagField = "_tag".text
val constdecl = "const".text

fun tParameters(tns: list<tName>): doc
  ntParameters(tns.map(fn(tn) (tn.getName, tn.tNameType)))

fun resultType(tp: ktype): <pure,compFlags> ktype
  match tp.splitFunScheme
    Just((_, _, _, _, res)) -> res
    _ -> fail("backend/c/from-core resultType: not a function type: " ++ tp.show) // TODO: Pretty type
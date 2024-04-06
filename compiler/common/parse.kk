//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

import compiler/syntax/layout
import compiler/syntax/lexer2
import compiler/syntax/lexeme
import compiler/syntax/syntax
import syntax
import name
import name-prim
import range

effect astError
  final ctl astError(e: string, r: range): a

effect astParse
  val sourceInfo: source
  fun addWarning(w: string, r: range): ()
  fun ppeek(): maybe<lexeme>
  fun undelimit(msg: string): ()
  fun reset(msg: string): ()
  fun delimit(msg: string): ()
  fun pnext(): maybe<lexeme>
  fun peof(): ()
  fun tookInput(msg: string): bool
  fun ptrace(s: string): ()
  fun takeAll(): list<lexeme>
  fun putAll(lexemes: list<lexeme>): ()

fun pdelimit(msg: string, f: () -> <astParse,astError|e> a): <astParse,astError|e> a
  delimit(msg)
  with override
    final ctl astError(e, r) 
      undelimit(msg)
      astError("\nWhen parsing " ++ msg ++ " " ++ e, r)
  val x = f()
  undelimit(msg)
  x

fun peek(): ast lexeme
  val p = ppeek()
  match p
    Just(l) -> l
    Nothing -> astError("unexpected end of file", rangeNull)

fun next(): ast lexeme
  val p = pnext()
  match p
    Just(l) -> l
    Nothing -> astError("unexpected end of file", rangeNull)

alias ast = <astParse, astError, pure, fsys>
fun lexParse(insSemi: bool, preprocess: list<lexeme> -> pure list<lexeme>, p: () -> <console,ast|e> a, sourceName: string, input: string): <console,astError,fsys,pure|e> a
  val src = Source(sourceName, input)
  val lexes = lex(src, 1, input)
  with parseLexemes(src, preprocess(layout(insSemi, lexes)))
  p()
  
fun parseLexemes(src: source, lexemes0: list<lexeme>, p: () -> <console,ast|e> a): <console,astError,fsys,pure|e> a
  var lexemes := lexemes0
  var history := Cons((ctx _, "top", 0), Nil)
  val debug = True
  with override
    final ctl astError(e: string, r: range)
      astError("Got error: " ++ e ++ "\n" ++ " when parsing:\n\t" ++ lexemes.take(2).map(show).join("\n\t"), r)
  with handler
    val sourceInfo = src
    fun takeAll()
      val l = lexemes
      lexemes := Nil // TODO: This ruins the history -- especially with delimiting
      // history := Cons((ctx _, "top", 0), Nil)
      l
    fun putAll(lexemes': list<lexeme>)
      lexemes := lexemes' // TODO: This ruins the history -- especially with delimiting
      // history := Cons((ctx _, "top", 0), Nil)
    fun addWarning(w: string, r: range)
      ()
    fun pnext()
      match lexemes
        Cons(l, rst) ->
          lexemes := rst 
          match history
            Cons((h, msg, i), tl) ->
              history := Cons((h ++ ctx Cons(l, _), msg, i + 1), tl)
            Nil -> 
              astError("unexpected top of context", rangeNull)
          Just(l)
        Nil -> Nothing
    fun reset(msg)
      match history
        Cons((h, str, _), rst) -> 
          if str != msg then
            trace("Resetting " ++ str ++ " but expected " ++ msg)
            throw("Reset error")
          else
            lexemes := h ++. lexemes
            history := rst
            if debug then
              trace("Resetting " ++ str ++ "\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ " at " ++ lexemes.head.map(show).default("eof") ++ "\nputting back:\n\t" ++ (h ++. Nil).map(show).join("\n\t"))
        Nil ->
          astError("mismatched reset", rangeNull)
    fun delimit(msg)
      history := Cons((ctx _, msg, 0), history)
    fun undelimit(msg)
      match history
        Cons((lexes, str, _), Cons((lexes2, str2, i2), rst)) ->
          if str == msg then
            history := Cons((lexes2 ++ lexes, str2, i2), rst)
          else
            trace("Undelimiting " ++ str ++ " but expected " ++ msg)
            throw("Undelimit error")
        _ ->
          throw("Undelimiting from top")
    fun ppeek()
      match lexemes
        Cons(l, _) -> Just(l)
        Nil -> Nothing
    fun peof()
      if debug then
        trace("Parsing eof\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ "\n\nHad leftovers: " ++ lexemes.map(fn(x) x.show).join("\n"))
      match lexemes
        Cons(l, _) ->
          astError("peof expected end of file", l.range)
        Nil ->
          ()
    fun tookInput(str)
      match history
        Cons((_, msg, i), _) ->
          if str != msg then
            trace("Checking if input was taken for " ++ str ++ " but expected " ++ msg)
            throw("Take input error")
          else
            i != 0
        Nil ->
          False
    fun ptrace(s: string)
      if debug then
        trace(s ++ "\n  " ++ history.map(fn(x) "When parsing " ++ x.snd).join("\n\t") ++ " next token: " ++ lexemes.take(1).map(show).join(","))
  mask<local>{p()}


fun pmany(kind: string, l: () -> <ast|e> a): <ast|e> list<a>
  match optionMaybe("many " ++ kind, l)
    Just(r) -> Cons(r, pmany(kind, l))
    Nothing -> Nil

fun pmany1(kind: string, l: () -> <ast|e> a): <ast|e> list<a>
  match optionMaybe("many " ++ kind, l)
    Just(r) -> Cons(r, pmany(kind, l))
    Nothing -> astError("at least 1 of " ++ kind, peek().range)

fun pmanyend(kind: string, l: () -> <ast|e> a, p: () -> <ast|e> b): <ast|e> list<a>
  match optionMaybe("many " ++ kind, l)
    Just(r) -> 
      match optionMaybe("sep " ++ kind, p)
        Just(_) -> Cons(r, pmanyend(kind, l, p))
        Nothing -> Cons(r, Nil)
    Nothing -> Nil

fun pmanyend1(kind: string, l: () -> <ast|e> a, p: () -> <ast|e> b): <ast|e> list<a>
  match optionMaybe("many " ++ kind, l)
    Just(r) -> 
      match optionMaybe("sep " ++ kind, p)
        Just(_) -> Cons(r, pmanyend(kind, l, p))

fun token(msg: string, f: (lexeme) -> <ast|e> maybe<a>): <ast|e> a
  val t = peek()
  match f(t) 
    Just(a) -> 
      next() 
      ptrace("Consuming " ++ t.show)
      a
    Nothing ->
      astError("expecting " ++ msg, peek().range)

// Version of maybe that does backtrack
fun maybe<e>(str: string, p: () -> <ast|e> a): <ast|e> maybe<a>
  delimit(str)
  with override
    return(r)
      undelimit(str)
      Just(r)
    final ctl astError(e, r) 
      reset(str)
      Nothing
  p()

fun maybeList(p: () -> <ast|e> list<a>): <ast|e> list<a>
  match maybe("list", p)
    Just(r) -> r
    Nothing -> []

fun try(str: string, p: () -> <ast|e> a): <ast|e> a
  delimit(str)
  with override
    return(r) 
      undelimit(str)
      r
    final ctl astError(e, r) 
      reset(str)
      astError(e,r)
  p()
  

// Version of maybe that doesn't backtrack
fun optionMaybe(str: string, p: () -> <ast|e> a): <ast|e> maybe<a>
  with pdelimit(str)
  with override
    return(r)
      Just(r)
    final ctl astError(e, r)
      if tookInput(str) then
        astError(e, r)
      else
        Nothing 
  p()
  

fun choicesnb(str: string, ps: list<() -> <ast|e> a>): <ast|e> a
  with pdelimit(str)
  fun find(ps': list<() -> <ast|e> a>): <ast|e> a
    match ps'
      Cons(p, rst) -> 
        match optionMaybe(str, p)
          Just(r) -> r
          Nothing -> find(rst)
      Nil -> astError("expected " ++ str, peek().range)
  find(ps)

fun choices(str: string, ps: list<() -> <ast|e> a>): <ast|e> a
  fun find(ps': list<() -> <ast|e> a>): <ast|e> a
    match ps'
      Cons(p, rst) -> 
        match maybe(str, p)
          Just(r) -> r
          Nothing -> find(rst)
      Nil -> astError("expected " ++ str, peek().range)
  find(ps)

fun makeParseError(r: range, e: string)
  astError("invalid syntax" ++ e.list.drop-while(fn(x) x != ':').string, r)

fun braced(p)
  val v = optionMaybe("braced") 
    pLcurly()
    pmany("semicolons", pSemicolon)
    val x = p()
    pmany("semicolons", pSemicolon)
    pRcurly()
    x
  match v
    Just(v') -> v'
    Nothing -> p()

fun semiBraces(kind, p)
  val rng1 = pLcurly()
  val xs = semis(kind, p)
  val rng2 = pRcurly()
  (xs, rng1.combine(rng2))

fun semis(kind, p)
  pmanyend(kind, p, pSemi1)

val pSepBy = pmanyend
val pSepBy1 = pmanyend1

fun pSemi1()
  pmany1("semicolons", pSemicolon)

fun parens(p)
  val l = pLparen()
  val x = p()
  val r = pRparen()
  (x, Range(l.start, r.end))

fun angles(p)
  val l = pLangle()
  val x = p()
  val r = pRangle()
  (x, Range(l.start, r.end))

fun parensCommas(p)
  parens
    pSepBy("comma", p, pComma)

fun parseRange(msg: string, f: (lexeme) -> <ast|e> bool): <ast|e> range
  token(msg, fn(x) if f(x) then Just(x) else Nothing).range

inline fun pLapp()
  pLparen()

inline fun pLidX()
  pLbracket()

inline fun pBar()
  pKeyword("|")

inline fun pComma()
  pSpecial(",")

inline fun pSemicolon(): <ast> lexeme
  token("semicolon") fn(x) 
    if x.is-semicolon then Just(x) else Nothing

fun pLbracket()
  parseRange("(", fn(x) x.lex.is-lbracket)

fun pRbracket()
  parseRange(")", fn(x) x.lex.is-rbracket)

fun pLparen()
  parseRange("(", fn(x) x.lex.is-lparen)

fun pRparen()
  parseRange(")", fn(x) x.lex.is-rparen)

fun pLangle()
  parseRange("<", fn(x) x.lex.is-langle)

fun pRangle()
  parseRange(">", fn(x) x.lex.is-rangle)

fun pLcurly()
  parseRange("{", fn(x) x.lex.is-lcurly)

fun pRcurly()
  parseRange("}", fn(x) x.lex.is-rcurly)

fun pTBinderId()
  choicesnb("tBinderId", [pTypeId, pTList, pTTuple, pTEmptyOrExtend])

fun pTEmptyOrExtend()
  val rng1 = pLangle()
  choicesnb("empty or extend effect", [
    {
      pBar()
      val rng2 = pRangle()
      (nameEffectEmpty, rng1.combine(rng2))
    },{
      val rng2 = pRangle()
      (nameEffectEmpty, rng1.combine(rng2))
    }
  ])

fun pConstructorId()
  choices("constructor", [pTTuple, pTList, pConId])

fun pTList(): <ast> (name, range)
  val rng1 = pSpecial("[")
  val rng2 = pSpecial("]")
  (nameTpList.unqualify, rng1.combine(rng2))

fun pTTuple(): <ast> (name, range)
  val rng1 = pLparen()
  val cs = pmany("comma", pComma)
  val rng2 = pRparen()
  (nameTuple(cs.length + 1).unqualify, rng1.combine(rng2))

fun pImportAlias()
  val (name1, rng1) = pModulePath()
  val r = maybe("import alias")
    pKeyword("=")
    pModulePath()
  match r
    Just((name2, rng2)) -> (name1, name2, rng2)
    Nothing -> (name1, name1, rng1)

fun pParamId()
  choices("param id", [pIdentifier, pWildcard])

fun pParamInfo()
  choices("param info", [{
    pSpecialOp("^")
    Borrow
  }, {Own}])

fun pIdentifier()
  ensureUnqualified("identifier", pQIdentifier)

fun pFipAlloc()
  parens
    choices("alloc", [
      { val (i, _) = pInteger(); AllocAtMost(i) },
      { val _ = pSpecialId("n"); AllocFinitely },
      { AllocAtMost(0) }
    ])

fun pFip()
  val isTail = choices("tail", [{pSpecialId("tail"); True}, {False}])
  choices("fip", [{
    val rng = pSpecialId("fip")
    val (alloc, _) = pFipAlloc()
    if isTail then
      addWarning("fip function already implies 'tail'", rng)
    Fip(alloc)
    }, 
    {
    pSpecialId("fbip")
    val (alloc, _) = pFipAlloc()
    Fbip(alloc, isTail)
    }, 
    {NoFip(isTail)}])

fun pInline()
  choicesnb("inline", [{
    pSpecialId("inline")
    InlineAlways
  }, {
    pSpecialId("noinline")
    InlineNever
  }, {InlineAuto}])

inline fun pQIdentifier()
  choices("qidentifier", [pQVarId, pQIdOp])

inline fun pQConstructor()
  pQConId()

inline fun pQOperator()
  pQOp()

fun pFunId()
  choicesnb("function id", [
    {pIdentifier()},
    {
      val rng1 = pSpecialId("[")
      val rng2 = pSpecialId("]")
      (nameIndex, Range(rng1.start, rng2.end))
    },
    {
      val (s, rng) = pStringLit()
      (newName(s), rng)
    }
    ])

fun pVarId()
  ensureUnqualified("variable id", pQVarId)

fun pIdOp()
  ensureUnqualified("operator", pQIdOp)

fun pConId()
  choices("Constructor", [
    { ensureUnqualified("constructor", pQConId) },
    { val (s, rng) = pStringLit(); (newName(s), rng)}
  ])

fun pOp()
  ensureUnqualified("operator", pQOp)

fun pTypeId()
  val (name, rng) = pQTypeId()
  if name.isQualified then
    astError("expected unqualified type name", rng)
  else
    (name, rng)

fun ensureUnqualified(str, p)
  val (n, r) = p()
  if n.isQualified then 
    astError("expected unqualified " ++ str, r)
  else
    (n, r)

fun pQTypeId()
  with try("qualified typeId")
  val (name, range) = choicesnb("qTypeId", [pQVarId, pTypeIdCtx])
  if !name.isTypeVar then 
    (name, range)
  else astError("type name (and not type variable)", range)

fun pTypeIdCtx()
  ("ctx".newName, pKeyword("ctx"))

fun pQOp()
  token("operator") fn(a)
    match a
      Lexeme(rng, LexOp(id)) -> 
        Just((id, rng))

fun pPrefixOp()
  token("prefix operator") fn(a)
    match a
      Lexeme(rng, LexPrefix(id)) -> 
        Just(Var(id, True, rng))
      _ -> Nothing

fun pQVarId()
  token("variable id") fn(a)
    match a
      Lexeme(rng, LexId(id)) -> 
        Just((id.showPlain.newName, rng))
      _ -> Nothing

fun pQIdOp()
  token("operator id") fn(a)
    match a
      Lexeme(rng, LexIdOp(id)) -> 
        Just((id, rng))
      _ -> Nothing

fun pQConId()
  token("constructor id") fn(a)
    match a
      Lexeme(rng, LexCons(id)) -> 
        Just((id, rng))
      _ -> Nothing

fun pModulePath(): <ast> (name, range)
  token("module path") fn(x)
    match x 
      Lexeme(rng, LexId(id)) -> 
        Just((id.showPlain.newName, rng))
      _ -> Nothing

fun pWildcard()
  token("wildcard") fn(a)
    match a
      Lexeme(rng, LexWildCard(id)) -> 
        Just((if id.showPlain == "_" then uniqueRangeName(rng, "_w") else id, rng))
      _ -> Nothing

fun pInteger()
  token("integer") fn(l)
    match l
      Lexeme(_, LexInt(i)) -> Just((i, l))
      _ -> Nothing

fun pFloat()
  token("float") fn(l)
    match l
      Lexeme(_, LexFloat(d)) -> Just((d, l))
      _ -> Nothing

fun pCharLit()
  token("char literal") fn(x) 
    match x
      Lexeme(rng, LexChar(s)) -> Just((s, rng))
      _ -> Nothing

fun pStringLit()
  token("string literal") fn(x) 
    match x
      Lexeme(rng, LexString(s)) -> Just((s, rng))
      _ -> Nothing

fun pSpecialId(s: string)
  token(s) fn(x)
    match x.lex
      LexId(id) | id.showPlain == s -> Just(x.range)
      _ -> Nothing


fun pSpecialId(s: string, alternates: list<string>)
  token(s) fn(x)
    match x.lex
      LexId(id) | id.showPlain == s -> Just(x.range)
      LexId(id) | alternates.any(fn(v) v == id.showPlain) -> 
        addWarning("using deprecated keyword " ++ id.showPlain ++ ", use " ++ s ++ " instead", x.range)
        Just(x.range)
      _ -> Nothing

inline fun pSpecial(s: string): <ast> range
  pSpecial(s, [])

fun pSpecial(s: string, alternates: list<string>): <ast> range
  token(s) fn(x)
    match x.lex
      LexSpecial(s') | s == s' -> Just(x.range)
      LexSpecial(s') | alternates.any(fn(v) v == s') -> 
        addWarning("using deprecated keyword " ++ s' ++ ", use " ++ s ++ " instead", x.range)
        Just(x.range)
      _ -> Nothing

fun pSpecialOp(s)
  token(s) fn(x)
    match x.lex
      LexOp(s') | s == s'.showPlain -> Just(x.range)
      _ -> Nothing

fun pSpecialConId(s)
  token(s) fn(x)
    match x.lex
      LexCons(s') | s == s'.showPlain -> Just(x.range)
      _ -> Nothing

inline fun pKeyword(s: string): <ast> range
  pKeywordBase(s, []).range

inline fun pKeyword(s: string, alts: list<string>): <ast> range
  pKeywordBase(s, alts).range

fun pKeywordBase(s: string, alternates: list<string>): <ast> lexeme
  token("keyword " ++ s) fn(x)
    match x.lex
      LexKeyword(s', _) | s == s' -> Just(x)
      LexKeyword(s', _) | alternates.any(fn(v) v == s') -> 
        addWarning("using deprecated keyword " ++ s' ++ ", use " ++ s ++ " instead", x.range)
        Just(x)
      _ -> Nothing

fun pDocKeyword(s: string): <ast> (range, string)
  pDocKeyword(s, [])

fun pDocKeyword(s: string, alternates: list<string>): <ast> (range, string)
  match pKeywordBase(s, alternates)
    Lexeme(rng, LexKeyword(_, doc)) -> (rng, doc)
    _ -> astError("expected " ++ s, rangeNull)

fun uniqueRangeHiddenName(pre: string, rng: range): name
  val pos = rng.start
  new-hidden-name(pre ++ "_" ++ pos.line.show ++ "_" ++ pos.col.show)

fun uniqueRangeName(rng: range, pre: string): name
  val pos = rng.start
  newName(pre ++ "-l" ++ pos.line.show ++ "-c" ++ pos.col.show)

fun adjustRange(ue: userExpr, r: range): userExpr
  Parens(ue, nameNil, r)

fun adjustTpRange(r: range, ut: userType): userType
  TpParens(ut, r)

fun unimplemented()
  astError("unimplemented", peek().range)
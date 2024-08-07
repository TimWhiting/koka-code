//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 8/6/24: Commit f31585c

import compiler/common/color-scheme
import compiler/common/range
import compiler/common/name
import compiler/lib/printer
import compiler/lib/pprint
import compiler/syntax/lexeme
import compiler/syntax/lexer
import compiler/syntax/layout
import std/os/path
// TODO: Isocline stuff

// TODO: HighlightPrint, FmtPrint, FmtAttr, HighlightInput, lex-comment 


// -----------------------------------------------------------
// Easy syntax highlighting
// ----------------------------------------------------------
// | Print source in color, given a color scheme, source name, 
// initial line number, the input string, and a 'Printer'.
fun source/highlight(source-name: path, line-no: int, input: string): <colorSchemeEffect> doc
  empty

// fun token/highlight(l: lexeme, )

fun highlight/show(Lexeme(_, lex): lexeme): exn string
  match lex
    LexInt() -> lex.show
    LexFloat() -> lex.show
    LexString(s) -> s.show
    LexChar(c) -> c.show
    LexId(id) -> id.show
    LexIdOp(id) -> (if id.is-qualified then id.qualifier.show ++ "/" else "") ++ "(" ++ id.unqualify.show-plain ++ ")"
    LexOp(id) -> id.show-plain
    LexPrefix(id) -> id.show-plain
    LexWildCard(id) -> id.show
    LexModule(id) -> id.show
    LexCons(id) -> id.show
    LexTypedId(id) -> id.show-plain
    LexKeyword(kw) -> kw.normalize
    LexSpecial(s) -> s.normalize
    LexComment(s) -> s
    LexWhite(w) -> w
    LexInsLCurly -> ""
    LexInsRCurly -> ""
    LexInsSemi -> ""
    LexError -> ""

fun normalize(s: string)
  match s.slice.next
    Just((c, rst)) -> 
      val x = rst.string.split(".")
      c.string ++ x.head.unjust

fun is-keyword-op(s: string)
  match s
    "=" -> False
    _ -> 
      match s.slice.next
        Just((c, _)) -> c.is-alpha
        Nothing -> False

type highlight-ctx
  CtxType(nesting: list<nesting>, str: string)
  CtxNormal

type nesting
  NestParen
  NestBracket
  NestAngle

fun nesting/(==)(n1: nesting, n2: nesting)
  match (n1, n2)
    (NestParen, NestParen) -> True
    (NestBracket, NestBracket) -> True
    (NestAngle, NestAngle) -> True
    _ -> False

type token<a>
  TokId(id: name, str: string)
  TokOp(id: name, str: string)
  TokSpecial
  TokKeyword
  TokTypeVar
  TokTypeId(id: name)
  TokTypeOp(id: name)
  TokTypeSpecial
  TokTypeKeyword
  TokTypeParam
  TokModule(nm: name)
  TokCons(nm: name)
  TokNumber
  TokString
  TokComment
  TokRichComment(r: list<token-comment<a>>)
  TokWhite
  TokError

type token-comment<a>
  ComText(str: string)
  ComEmph(str: string)
  ComPre(str: string)
  ComPreBlock(str: string)
  ComUrl(str: string)
  ComLine(str: string)
  ComCode(code: list<a>, str: string)
  ComCodeBlock(blk: string, code: list<a>, str: string)
  ComCodeLit(lit: string, code: list<a>, str: string)
  ComPar
  ComIndent(ind: int)

fun comment-flatten(comms: list<token-comment<a>>, f: string -> a): list<a>
  with c <- comms.flatmap
  match c
    ComText(x) -> [f(x)]
    ComEmph(x) -> [f(x)]
    ComPre(x) -> [f(x)]
    ComPreBlock(x) -> [f(x)]
    ComUrl(x) -> [f(x)]
    ComLine(x) -> [f(x)]
    ComCode(c, _) -> c
    ComCodeBlock(_, c, _) -> c
    ComCodeLit(_, c, _) -> c
    ComPar -> []
    ComIndent(i) -> [f(" ".repeat(i))]

fun nesting(n: highlight-ctx): int
  match n
    CtxType(n) -> n.length
    _ -> 0

fun highlight(fmt: (token<lexeme>, lexeme, string) -> pure a, transform: list<lexeme> -> pure list<lexeme>, c: highlight-ctx, source: path, lineNo: int, str: string): pure list<a>
  val xs = lexer(source.string, lineNo, str)
  highlight-lexemes(transform, fmt, c, ctx _, xs.combine-line-comments.transform)

fun highlight-lexemes(transform: list<lexeme> -> pure list<lexeme>, fmt: (token<lexeme>, lexeme, string) -> pure a, c: highlight-ctx, acc: ctx<list<a>>, lexes: list<lexeme>): pure list<a>
  match lexes
    Cons(l, lexes') ->
      val (ctx', content) = highlight-lexeme(transform, fmt, c, l, lexes')
      highlight-lexemes(transform, fmt, ctx', acc ++ ctx Cons(content, _), lexes')
    Nil -> acc ++. Nil

fun highlight-lexeme(transform: list<lexeme> -> pure list<lexeme>, fmt0: (token<lexeme>, lexeme, string) -> pure a, ctx0: highlight-ctx, lexeme: lexeme, lexs: list<lexeme>): pure (highlight-ctx, a)
  val Lexeme(rng, lex) = lexeme
  fun fmt(tok, s)
    fmt0(tok, lexeme, s)
  fun show-id(n: name): string
    if n.nameStem == "!" || n.nameLocalQual == "~" then n.show-plain else n.show
  fun show-op(n: name): string
    match n.nameStem.slice.next
      Just((c, _)) | c.is-alpha-num -> "`" ++ n.show ++ "`"
      _ -> n.show-plain
  fun highlight-comment(com)
    match com
      ComCode(lexs', s) -> ComCode(highlight-lexemes(transform, fmt0, CtxNormal, ctx _, lexs'.transform), s)
      ComCodeBlock(cls, lexs', s) -> ComCodeBlock(cls, highlight-lexemes(transform, fmt0, CtxNormal, ctx _, lexs'.transform), s)
      ComCodeLit(cls, lexs', s) -> ComCodeLit(cls, highlight-lexemes(transform, fmt0, CtxNormal, ctx _, lexs'.transform), s)
      ComText(s) -> ComText(s)
      ComEmph(s) -> ComEmph(s)
      ComUrl(s) -> ComUrl(s)
      ComPre(s) -> ComPre(s)
      ComPreBlock(s) -> ComPreBlock(s)
      ComLine(s) -> ComLine(s)
      ComPar -> ComPar
      ComIndent(n) -> ComIndent(n)
  val ctx1 = ctx0.adjust-context(lex, lexs)
  val con0 = 
    match lex
      LexId(id) ->
        val tok = 
          if ctx1.is-ctxType then 
            match lexs.drop-while(is-white)
              Cons(Lexeme(_, LexKeyword(":"))) | ctx1.nesting > 0 -> TokTypeParam
              _ -> if id.is-type-var then TokTypeVar else TokTypeId(id)
          else TokId(id, "")
        fmt(tok, id.unqualify.show-id)
      LexWildCard(id) -> fmt(if ctx1.is-ctxType then TokTypeVar else TokId(id, ""), id.show)
      LexOp(id) -> 
        val token = 
          if ctx1.is-ctxType then 
            val idp = id.show-plain
            if ["<", ">", "|", "::"].any(fn(id0) idp == id0) then TokTypeSpecial 
            else TokTypeOp(id)
          else TokOp(id, "")
        fmt(token, id.unqualify.show-op)
      LexPrefix(id) -> fmt(TokOp(id, ""), id.unqualify.show-id)
      LexIdOp(id) -> fmt(TokOp(id, ""), id.unqualify.show-id)
      LexInt -> fmt(TokNumber, lex.show)
      LexFloat -> fmt(TokNumber, lex.show)
      LexString(s) -> fmt(TokString, s.show)
      LexChar(c) -> fmt(TokString, c.show)
      LexModule(id, mid) -> fmt(TokModule(mid), id.show)
      LexCons(id) -> fmt(if ctx1.is-ctxType then TokTypeId(id) else TokCons(id), id.unqualify.show-id)
      LexTypedId(id, tp) -> fmt(TokId(id, tp), id.unqualify.show-id)
      LexKeyword(":") -> fmt(TokTypeKeyword, ":")
      LexKeyword(k) -> fmt(if ctx1.is-ctxType then TokTypeKeyword else TokKeyword, k.normalize)
      LexSpecial(s) -> fmt(if ctx1.is-ctxType then TokTypeSpecial else TokSpecial, s.normalize)
      LexComment(s) -> fmt(TokRichComment(lex-comment(rng.source.name, rng.start.line, s)), s)
      LexWhite(w) -> fmt(TokWhite, w)
      LexInsLCurly -> fmt(TokWhite, "")
      LexInsRCurly -> fmt(TokWhite, "")
      LexInsSemi -> fmt(TokWhite, "")
      LexError(msg) -> fmt(TokError, msg)
  (ctx1, con0)

fun adjust-context(c: highlight-ctx, l: lex, lexes: list<lexeme>)
  match c
    CtxNormal ->
      match l
        LexOp(o) | o.show-plain == "::" -> CtxType([], "::")
        LexKeyword(":") -> CtxType([], ":")
        LexKeyword("type") -> CtxType([], "type")
        LexKeyword("cotype") -> CtxType([], "cotype")
        LexKeyword("rectype") -> CtxType([], "rectype")
        LexKeyword("alias") -> CtxType([], "alias")
        LexKeyword("effect") -> CtxType([], "effect")
        LexKeyword("struct") -> 
          match lexes.drop-while(is-white)
            Cons(Lexeme(_, LexSpecial("("))) -> CtxType([], "struct-tuple")
            _ -> CtxType([], "struct")
        _ -> CtxNormal
    CtxType(nest0, decl) ->
      fun push(n: nesting)
        CtxType(Cons(n, nest0), decl)
      fun pop(n: nesting, nest: list<nesting>)
        match nest
          [] -> CtxNormal
          Cons(m, ms) | n == m -> CtxType(ms, decl)
                      | True -> pop(n, ms)
      match l
        LexId -> c
        // LexCons id -> c
        LexOp(op) | op.show-plain == "<" -> push(NestAngle)
                  | op.show-plain == ">" -> pop(NestAngle, nest0)
                  | True -> c
        LexWildCard -> c
        LexWhite(w) | w.count < 2 -> c
        LexComment -> c
        LexKeyword("|") -> c
        LexKeyword(".") -> c
        LexKeyword(":") -> c
        LexKeyword("->") -> c
        LexKeyword("with") -> c
        LexKeyword("forall") -> c
        LexKeyword("some") -> c
        LexKeyword("exists") -> c
        LexSpecial("?") -> c // optional types
        LexKeyword("=") | decl == "alias" -> c
        LexSpecial(",") | nest0.is-cons || decl == "struct-tuple" -> c
        LexSpecial("(") | decl == "struct-tuple" -> CtxType(Cons(NestParen, nest0), "struct")
                        | decl != "struct" -> push(NestParen)
        LexSpecial("[") -> push(NestBracket)
        LexSpecial(")") -> pop(NestParen, nest0)
        LexSpecial("]") -> pop(NestBracket, nest0)
        _ -> adjust-context(CtxNormal, l, lexes)

// Parse comment formatters
fun lex-comment(source: string, lineno: int, content: string): list<token-comment<lexeme>>
  []// TODO: 
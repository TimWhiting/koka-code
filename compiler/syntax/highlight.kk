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
import std/core-extras
// TODO: Isocline stuff

// TODO: FmtAttr

effect fmt
  fun fmt(t: token<lexeme>, l: lexeme, s: string): token<lexeme>
  val source-file: string

alias highlight-eff = <colorSchemeEffect,coloredPrinter,printer,pure>
alias highlight = <fmt,pure>
// -----------------------------------------------------------
// Easy syntax highlighting
// ----------------------------------------------------------
// | Print source in color, given a color scheme, source name, 
// initial line number, the input string, and a 'Printer'.
fun highlight-print(source-name: path, line-no: int, input: string): <colorSchemeEffect,coloredPrinter,printer,pure> ()
  val cls = ColorScheme()
  with handler 
    val source-file = source-name.string
    fun fmt(token, lex, s)
      match token
        TokId -> write(s)
        TokOp -> write(s)
        TokTypeVar -> s.print-colored(cls.colorTypeVar)
        TokTypeId -> s.print-colored(cls.colorTypeCon)
        TokTypeOp -> s.print-colored(cls.colorTypeCon)
        TokTypeSpecial -> s.print-colored(cls.colorTypeSpecial)
        TokTypeParam -> s.print-colored(cls.colorTypeParam)
        TokModule -> s.print-colored(cls.colorModule)
        TokCons -> s.print-colored(cls.colorCons)
        TokNumber -> s.print-colored(cls.colorNumber)
        TokString -> s.print-colored(cls.colorString)
        TokSpecial -> s.print-colored(cls.colorSpecial)
        TokTypeKeyword ->
          if !s.is-keyword-op then s.print-colored(cls.colorTypeKeyword)
          else s.print-colored(cls.colorTypeKeywordOp)
        TokKeyword -> s.print-colored(cls.colorKeyword)
        TokComment -> s.print-colored(cls.colorComment)
        TokRichComment -> s.print-colored(cls.colorComment)
        TokWhite -> write(s)
        TokError -> ()
      token
  highlight(id, CtxNormal, line-no, input)
  ()


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

fun fmt/highlight(transform: list<lexeme> -> pure list<lexeme>, c: highlight-ctx, lineNo: int, str: string): highlight list<token<lexeme>>
  val xs = lexer(source-file, lineNo, str)
  highlight-lexemes(transform, c, [], xs.combine-line-comments.transform)

fun highlight-lexemes(transform: list<lexeme> -> pure list<lexeme>, c: highlight-ctx, acc: list<token<lexeme>>, lexes: list<lexeme>): highlight list<token<lexeme>>
  match lexes
    Cons(l, lexes') ->
      val (ctx', content) = highlight-lexeme(transform, c, l, lexes')
      highlight-lexemes(transform, ctx', Cons(content, acc), lexes')
    Nil -> acc.reverse

fun highlight-lexeme(transform: list<lexeme> -> pure list<lexeme>, ctx0: highlight-ctx, lexeme: lexeme, lexs: list<lexeme>): highlight (highlight-ctx, token<lexeme>)
  val Lexeme(rng, lex) = lexeme
  fun show-id(n: name): string
    if n.nameStem == "!" || n.nameLocalQual == "~" then n.show-plain else n.show
  fun show-op(n: name): string
    match n.nameStem.slice.next
      Just((c, _)) | c.is-alpha-num -> "`" ++ n.show ++ "`"
      _ -> n.show-plain
  fun highlight-comment(com: token-comment<lexeme>): <pure,fmt> token-comment<token<lexeme>>
    match com
      ComCode(lexs', s) -> ComCode(highlight-lexemes(transform, CtxNormal, [], lexs'.transform), s)
      ComCodeBlock(cls, lexs', s) -> ComCodeBlock(cls, highlight-lexemes(transform, CtxNormal, [], lexs'.transform), s)
      ComCodeLit(cls, lexs', s) -> ComCodeLit(cls, highlight-lexemes(transform, CtxNormal, [], lexs'.transform), s)
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
        fmt(tok, lexeme, id.unqualify.show-id)
      LexWildCard(id) -> fmt(if ctx1.is-ctxType then TokTypeVar else TokId(id, ""), lexeme, id.show)
      LexOp(id) -> 
        val token = 
          if ctx1.is-ctxType then 
            val idp = id.show-plain
            if ["<", ">", "|", "::"].any(fn(id0) idp == id0) then TokTypeSpecial 
            else TokTypeOp(id)
          else TokOp(id, "")
        fmt(token, lexeme, id.unqualify.show-op)
      LexPrefix(id) -> fmt(TokOp(id, ""), lexeme, id.unqualify.show-id)
      LexIdOp(id) -> fmt(TokOp(id, ""), lexeme, id.unqualify.show-id)
      LexInt -> fmt(TokNumber, lexeme, lex.show)
      LexFloat -> fmt(TokNumber, lexeme, lex.show)
      LexString(s) -> fmt(TokString, lexeme, s.show)
      LexChar(c) -> fmt(TokString, lexeme, c.show)
      LexModule(id, mid) -> fmt(TokModule(mid), lexeme, id.show)
      LexCons(id) -> fmt(if ctx1.is-ctxType then TokTypeId(id) else TokCons(id), lexeme, id.unqualify.show-id)
      LexTypedId(id, tp) -> fmt(TokId(id, tp), lexeme, id.unqualify.show-id)
      LexKeyword(":") -> fmt(TokTypeKeyword, lexeme, ":")
      LexKeyword(k) -> fmt(if ctx1.is-ctxType then TokTypeKeyword else TokKeyword, lexeme, k.normalize)
      LexSpecial(s) -> fmt(if ctx1.is-ctxType then TokTypeSpecial else TokSpecial, lexeme, s.normalize)
      LexComment(s) -> fmt(TokRichComment(lex-comment(rng.start.line, s)), lexeme, s)
      LexWhite(w) -> fmt(TokWhite, lexeme, w)
      LexInsLCurly -> fmt(TokWhite, lexeme, "")
      LexInsRCurly -> fmt(TokWhite, lexeme, "")
      LexInsSemi -> fmt(TokWhite, lexeme, "")
      LexError(msg) -> fmt(TokError, lexeme, msg)
  (ctx1, con0)

fun adjust-context(c: highlight-ctx, l: lex, lexes: list<lexeme>): div highlight-ctx
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

// scanTag: ignore things inside "<tag...>" and "<script .. </script>" or "<style .. </style>" tags
fun scan-tag(n: int, lacc: ctx<list<token-comment<lexeme>>>, content: list<char>): <pure,fmt> list<token-comment<lexeme>>
  fun default()
    val (tag, clos) = content.span(fn(c) c != '>' && c != '\n')
    val (end, rest) = if clos.is-nil then ([], []) else ([clos.string.head-char.unjust], clos.tail)
    scan(if end.string.head-char.unjust == '\n' then n + 1 else n, lacc ++ ctx Cons(ComText(tag.string ++ end.string), _), [], rest)
  match content
    Cons('<', rest) ->
      val (tagName, _) = rest.span(is-alpha-num)
      val tag = tagName.map(to-lower).string
      if tag == "script" || tag == "style" then
        fun span-to-end-tag(acc: list<list<char>>, chs: list<char>)
          match chs
            Cons('<', Cons('/', cs)) ->
              val (name, ds) = cs.span(is-alpha-num)
              val (tagend, es) = ds.span(fn(c) c == ' ' || c == '\t' || c == '>')
              if name.map(to-lower).string == tag then
                (Cons(Cons('<', Cons('/', name ++ tagend)), acc).reverse.concat, es)
              else
                span-to-end-tag(Cons(['<', '/'], acc), cs)
            Cons('<', cs) -> span-to-end-tag(Cons(['<'], acc), cs)
            Nil -> (acc.reverse.concat, [])
            Cons ->
              val (pre, post) = chs.span(fn(c) c != '<')
              span-to-end-tag(Cons(pre, acc), post)
        val (elem, after) = span-to-end-tag([], content)
        val m = elem.filter(fn(e) e == '\n').length
        scan(n + m, lacc ++ ctx Cons(ComText(elem.string), _), [], after)
      else
        default()
    _ -> default()

fun scan-math(n: int, lacc: ctx<list<token-comment<lexeme>>>, content: list<char>): <pure,fmt> list<token-comment<lexeme>>
  val (math, clos) = content.span(fn(c) c != '$' && c != '\n')
  val (end, rest) = if clos.is-nil then ([], []) else ([clos.string.head-char.unjust], clos.tail)
  scan(if end.string.head-char.unjust == '\n' then n + 1 else n, lacc ++ ctx Cons(ComText("$" ++ math.string ++ end.string), _), [], rest)

// scanPre formatted ``pre``
fun scan-pre(m: int, n: int, lacc: ctx<list<token-comment<lexeme>>>, acc: list<char>, chs: list<char>): <pure,fmt> list<token-comment<lexeme>>
  match chs
    Cons('`', rest) ->
      val (pre, post) = rest.span(fn(c) c == '`')
      if m == pre.length + 1 then
        scan(n, lacc, Cons('`', pre ++ acc), post)
      else
        scan-pre(m, n, lacc, Cons('`', acc), rest)
    Cons('\n', rest) -> scan(n, lacc, acc, Cons('\n', rest)) // don't go through newlines
    Cons(c, rest) -> scan-pre(m, n, lacc, Cons(c, acc), rest)
    Nil -> scan(n, lacc, acc, [])

// scanCode "f(x)"
fun scan-code(n: int, com: (list<lexeme>, string) -> token-comment<lexeme>, lacc: ctx<list<token-comment<lexeme>>>, acc: list<char>, chs: list<char>): <pure,fmt> list<token-comment<lexeme>>
  match chs
    Cons('`', rest) -> end-code(n, com, lacc, acc, [], rest)
    Cons('\n', rest) -> end-code(n, com, lacc, acc, ['\n'], rest)
    Cons(c, rest) -> scan-code(n, com, lacc, Cons(c, acc), rest)
    Nil -> end-code(n, com, lacc, acc, [], [])

fun end-code(n: int, com: (list<lexeme>, string) -> token-comment<lexeme>, lacc: ctx<list<token-comment<lexeme>>>, acc: list<char>, post: list<char>, rest: list<char>): <pure,fmt> list<token-comment<lexeme>>
  val lexemes = lexer(source-file, n, acc.drop-while(is-space).reverse.string)
  scan(n, lacc ++ ctx Cons(com(lexemes, acc.reverse.string), _), post.reverse, rest)

fun comCode(l, s)
  ComCode(l, s)

fun comCodeBlock(cls)
  fn(l, s)
    ComCodeBlock(cls, l, s)

fun comCodeLit(cls)
  fn(l, s)
    ComCodeLit(cls, l, s)

fun scan-pre-block(m: int, n: int, lacc: ctx<list<token-comment<lexeme>>>, acc: list<char>, chs: list<char>): <pure,fmt> list<token-comment<lexeme>>
  match chs
    Cons('`', rest) ->
      val (pre, post) = rest.span(fn(c) c == '`')
      if m == pre.length + 1 then
        scan(n, lacc, Cons('`', pre ++ acc), post)
      else
        scan-pre-block(m, n, lacc, Cons('`', acc), rest)
    Cons(c, rest) -> scan-pre-block(m, if c == '\n' then n + 1 else n, lacc, Cons(c, acc), rest)
    Nil -> scan(n, lacc, acc, [])

fun scan-code-block(n: int, com: (list<lexeme>, string) -> token-comment<lexeme>, m: int, lacc: ctx<list<token-comment<lexeme>>>, acc: list<char>, chs: list<char>): <pure,fmt> list<token-comment<lexeme>>
  match chs
    Cons('/', Cons('/', Cons('/', Cons('/', rest)))) | on-line(acc, rest) ->
      scan-code-block2(n + 1, comCodeLit(""), n + 1, lacc, acc.reverse, [], rest.drop-line)
    Cons('`', Cons('`', Cons('`', rest))) | on-line(acc, rest) ->
      end-code-block(n + 1, com, m, lacc, [], acc, rest.drop-line)
    Cons(c, rest) -> scan-code-block(if c == '\n' then n + 1 else n, com, m, lacc, Cons(c, acc), rest)
    Nil -> end-code-block(n, com, m, lacc, acc.reverse, [], [])

fun scan-code-block2(n: int, com: (list<lexeme>, string) -> token-comment<lexeme>, m: int, lacc: ctx<list<token-comment<lexeme>>>, pre: list<char>, acc: list<char>, chs: list<char>): <pure,fmt> list<token-comment<lexeme>>
  match chs
    Cons('`', Cons('`', Cons('`', rest))) | on-line(acc, rest) ->
      end-code-block(n + 1, com, m, lacc, pre, acc, rest.drop-line)
    Cons(c, rest) -> scan-code-block2(if c == '\n' then n + 1 else n, com, m, lacc, pre, Cons(c, acc), rest)
    Nil -> end-code-block(n, com, m, lacc, pre, acc, [])
 
fun end-code-block(n: int, com: (list<lexeme>, string) -> token-comment<lexeme>, m: int, lacc: ctx<list<token-comment<lexeme>>>, pre: list<char>, acc: list<char>, rest: list<char>): <pure,fmt> list<token-comment<lexeme>>
  val src = acc.reverse.drop-line.string
  val lexes = lexer(source-file, m, src)
  scan(n, lacc ++ ctx Cons(com(lexes, if pre.is-nil then src else pre.string ++ "\n" ++ src), _), [], rest)

fun scan(lineno: int, lacc: ctx<list<token-comment<lexeme>>>, acc: list<char>, chs: list<char>): <pure,fmt> list<token-comment<lexeme>>
  match chs
    // Skip inside tags (so html renders correctly)
    Cons('<', Cons(c, rest)) | !c.is-space -> scan-tag(lineno, lacc ++ ctx Cons(ComText(acc.reverse.string), _), Cons('<', Cons(c, rest)))
    // Skip inside $ (so math renders correctly)
    Cons('$', Cons(c, rest)) -> scan-math(lineno, lacc ++ ctx Cons(ComText(acc.reverse.string), _), Cons(c, rest))
    // Code
    Cons('`', Cons(c, rest)) 
      | c != '`' -> scan-code(lineno, comCode, lacc ++ ctx Cons(ComText(acc.reverse.string), _), [], Cons(c, rest))
      | c == ':' -> scan-code(lineno, comCode, lacc ++ ctx Cons(ComText(acc.reverse.string), _), [':'], rest)
    Cons('`', Cons('`', Cons('`', Cons(c, rest)))) | acc.white-line && c != '`' ->
      val (pre, xpost) = Cons(c, rest).span(fn(c') c != '\n' && c' != '{' && c' != ' ')
      val (attr, post) = xpost.span(fn(c') c' != '\n')
      val cls = 
        match attr.drop-while(fn(c') c' != '.')
          Nil -> ""
          Cons(_, cs) -> cs.take-while(is-alpha-num).string
      val pres = pre.string
      val attrs = attr.string
      val ccode = if pres == "unchecked" then comCodeBlock(cls) else comCodeLit(cls)
      if pres == "unchecked" || pres == "koka" || pres == "" then
        scan-code-block(lineno + 1, ccode, lineno + 1, lacc ++ ctx Cons(ComText(acc.drop-line.string), _), [], post.drop-line)
      else
        scan-pre-block(3, lineno, lacc ++ ctx Cons(ComText(("```".list ++ pre ++ acc).reverse.string), _), [], post)
    Cons('`', rest) ->
      val (pre, post) = rest.span(fn(c) c != '`')
      val lacc' = lacc ++ ctx Cons(ComText(Cons('`', pre ++ acc).reverse.string), _)
      if acc.white-line && pre.length >= 2 then
        scan-pre-block(pre.length + 1, lineno, lacc', [], post)
      else
        scan-pre(pre.length + 1, lineno, lacc', [], post)
    // regular
    Cons('\n', rest) -> scan(lineno + 1, lacc, Cons('\n', acc), rest)
    Cons(c, rest) -> scan(lineno, lacc, Cons(c, acc), rest)
    Nil -> lacc ++. Cons(ComText(acc.reverse.string), Nil)

// Parse comment formatters
fun lex-comment(lineno: int, content: string): <pure,fmt> list<token-comment<lexeme>>
  scan(lineno, ctx _, [], content.list.filter(fn(c) c != '\r'))

fun on-line(pre: list<char>, post: list<char>): bool
  pre.white-line && post.white-line

fun white-line(s: list<char>): bool
  match s.drop-while(fn(c) c == ' ' || c == '\t' || c == '\r')
    Cons(c) -> c == '\n'
    [] -> True

fun drop-line(s: list<char>): list<char>
  match s.drop-while(fn(c) c == ' ' || c == '\t' || c == '\r')
    Cons('\n', rest) -> rest
    cs -> cs
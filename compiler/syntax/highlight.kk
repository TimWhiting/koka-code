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

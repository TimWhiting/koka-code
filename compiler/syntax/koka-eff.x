{
import compiler/common/name
import compiler/common/range
import compiler/syntax/lexeme
import std/num/float64
import std/core-extras
import std/data/word-set

effect koka-lex
  fun start-chunked(): ()
  fun end-chunked(): string
  fun add-chunk(s: sslice): ()
  fun get-rawdelim(): int
  fun set-rawdelim(i: int): ()
  fun do-emit(l: lex, start: alex-pos, end: alex-pos): ()

fun emit(l: lex): <alex,koka-lex> ()
  do-emit(l, get-start(), get-end())

}


%encoding "utf8"
%effects "koka-lex"

-----------------------------------------------------------
-- Character sets
-----------------------------------------------------------
$digit        = [0-9]
$hexdigit     = [0-9a-fA-F]
$lower        = [a-z]
$upper        = [A-Z]
$letter       = [$lower$upper]
$space        = [\ ]
$tab          = [\t]
$return       = \r
$linefeed     = \n
$graphic      = [\x21-\x7E]
$cont         = [\x80-\xBF]
$symbol       = [\$\%\&\*\+\~\!\\\^\#\=\.\:\-\?\|\<\>]
$special      = [\(\)\[\]\{\}\;\,]
$anglebar     = [\<\>\|]
$angle        = [\<\>]
$finalid      = [\']
$charesc      = [nrt\\\'\"]    -- "

-----------------------------------------------------------
-- Regular expressions
-----------------------------------------------------------
@newline      = $return?$linefeed

@utf8valid    = [\xC2-\xDF] $cont
              | \xE0 [\xA0-\xBF] $cont
              | [\xE1-\xEC] $cont $cont
              | \xED [\x80-\x9F] $cont
              | [\xEE-\xEF] $cont $cont
              | \xF0 [\x90-\xBF] $cont $cont
              | [\xF1-\xF3] $cont $cont $cont
              | \xF4 [\x80-\x8F] $cont $cont

@utf8unsafe   = \xE2 \x80 [\x8E-\x8F\xAA-\xAE]
              | \xE2 \x81 [\xA6-\xA9]

@utf8         = @utf8valid          

@linechar     = [$graphic$space$tab]|@utf8
@commentchar  = ([$graphic$space$tab] # [\/\*])|@newline|@utf8

@hexdigit2    = $hexdigit $hexdigit
@hexdigit4    = @hexdigit2 @hexdigit2
@hexesc       = x@hexdigit2|u@hexdigit4|U@hexdigit4@hexdigit2
@escape       = \\($charesc|@hexesc)
@stringchar   = ([$graphic$space] # [\\\"])|@utf8             -- " fix highlight
@charchar     = ([$graphic$space] # [\\\'])|@utf8
@stringraw    = ([$graphic$space$tab] # [\"])|@newline|@utf8  -- "

@idchar       = $letter | $digit | _ | \-
@lowerid      = $lower @idchar* $finalid*
@upperid      = $upper @idchar* $finalid*
@conid        = @upperid
@modulepath   = (@lowerid\/)+
@qvarid       = @modulepath @lowerid
@qconid       = @modulepath @conid
@symbols      = $symbol+ | \/
@qidop        = @modulepath \(@symbols\)
@idop         = \(@symbols\)

@sign         = [\-]?
@digitsep     = _ $digit+
@hexdigitsep  = _ $hexdigit+
@digits       = $digit+ @digitsep*
@hexdigits    = $hexdigit+ @hexdigitsep*
@decimal      = 0 | [1-9] (_? @digits)?
@hexadecimal  = 0[xX] @hexdigits
@integer      = @sign (@decimal | @hexadecimal)

@exp          = (\-|\+)? $digit+
@exp10        = [eE] @exp
@exp2         = [pP] @exp
@decfloat     = @sign @decimal (\. @digits @exp10? | @exp10)
@hexfloat     = @sign @hexadecimal (\. @hexdigits @exp2? | @exp2)

-----------------------------------------------------------
-- Main tokenizer
-----------------------------------------------------------
program :-
-- white space
<0> $space+               { fn() { emit(LexWhite(get-string()))} }
<0> @newline              { fn() { emit(LexWhite("\n")) } }
<0> "/*" $symbol*         { fn() { push-state(comment); start-chunked(); } }
<0> "//" $symbol*         { fn() { push-state(linecom); start-chunked(); } }
<0> @newline\# $symbol*   { fn() { push-state(linedir); start-chunked(); } }


-- qualified identifiers
<0> @qconid               { fn() { emit(LexCons(get-qname())) } }
<0> @qvarid               { fn() { emit(LexId(get-qname())) } }
<0> @qidop                { fn() { emit(LexIdOp(get-slice().strip-parens.newQName)) } }

-- identifiers
<0> @lowerid              { fn() {
    val s = get-string();
    if s.is-reserved then emit(LexKeyword(s, ""))
    elif s.is-malformed then emit(LexError(message-malformed))
    else emit(LexId(s.new-name))
  }}
<0> @conid                { fn() { emit(LexCons(get-name())) } }
<0> _@idchar*             { fn() { emit(LexWildCard(get-name())) } }

-- specials
<0> $special              { fn() { emit(LexSpecial(get-string())) } }

-- literals
<0> @decfloat             { fn() { val s = get-string(); emit(LexFloat(s.parse-float64.unjust, s)) } }
<0> @hexfloat             { fn() { val s = get-string(); emit(LexFloat(s.parse-float64.unjust, s)) } }
<0> @integer              { fn() { val s = get-string(); emit(LexInt(s.parse-int.unjust, s)) } }


-- type operators
<0> "||"                  { fn() { emit(LexOp(get-name())) } }
-- <0> $anglebar $anglebar+  { fn() { less(1, string(fn(s) if (s=="|") then LexKeyword(s, "") else LexOp(s.new-name))) } }

-- operators
<0> @idop                 { fn() { emit(LexIdOp(get-slice().strip-parens.new-name)) } }
<0> @symbols              { fn() {
    val s = get-string();  
    if s.is-reserved then emit(LexKeyword(s,""))
    elif s.is-prefix-op then emit(LexPrefix(s.new-name))
    else emit(LexOp(s.new-name))
   }}


-- characters
<0> \"                    { fn() { push-state(stringlit); start-chunked(); } } -- "
<0> r\#*\"                { fn() { push-state(stringraw); start-chunked(); push-rawdelim(); } } -- "

<0> \'\\$charesc\'        { fn() { emit(LexChar(get-slice().sslice/drop(2).next.unjust.tuple2/fst.char/from-char-esc)) }}
<0> \'\\@hexesc\'         { fn() { emit(LexChar(get-slice().sslice/drop(3).extend(-1).char/from-hex-esc)) }}
<0> \'@charchar\'         { fn() { emit(LexChar(get-slice().sslice/drop(1).next.unjust.tuple2/fst)) }}
<0> \'.\'                 { fn() { emit(LexError("illegal character literal: " ++ get-slice().sslice/drop(1).next.map(tuple2/fst).default(' ').show)) }}

-- catch errors
<0> $tab+                 { fn() { emit(LexError("tab characters: configure your editor to use spaces instead (soft tab)")) }}
<0> .                     { fn() { emit(LexError("illegal character: " ++ get-slice().show ++ (if (get-string() =="\t") then " (replace tabs with spaces)" else ""))) }}

--------------------------
-- string literals

<stringlit> @utf8unsafe   { fn() { unsafe-char("string") } }
<stringlit> @stringchar   { fn() { extend-slice(id) } }
<stringlit> \\$charesc    { fn() { extend-slice(sslice/from-char-esc) } }
<stringlit> \\@hexesc     { fn() { extend-slice(sslice/from-hex-esc) } }
<stringlit> \"            { fn() { pop-state(); val s = end-chunked(); emit(LexString(s)) } } -- " 
<stringlit> @newline      { fn() { pop-state(); end-chunked(); emit(LexError("string literal ended by a new line")) } }
<stringlit> .             { fn() { pop-state(); val s = end-chunked(); emit(LexError("illegal character in string: " ++ s.show)) } }

<stringraw> @utf8unsafe   { fn() { unsafe-char("raw string") } }
<stringraw> @stringraw    { fn() { extend-slice(id) } }
<stringraw> \"\#*         { fn() {
                            val delim = get-slice().count
                            val curdelim = get-rawdelim()
                            if delim == curdelim then
                              emit(LexString(end-chunked()))
                              pop-state()
                              pop-rawdelim()
                            elif delim > curdelim then // too many terminating hashes
                              emit(LexError("raw string: too many '#' terminators in raw string (expecting " ++ show(delim - 1) ++ ")"))
                              end-chunked()
                              pop-state()
                              pop-rawdelim()
                            else // continue
                              extend-slice(id)
                          }}
<stringraw> .             { fn() {
  emit(LexError("illegal character in raw string: " ++ end-chunked().show))
  pop-state()
  pop-rawdelim()
 }}


--------------------------
-- block comments

<comment> "*/"            { fn() {
  val st = pop-state()
  // TODO? end-chunked()
  if st == comment then extend-slice(id)
  else 
    emit(LexComment(end-chunked().list.filter(fn(c) c != '\r').string))
    pop-state()
    ()
}}
<comment> "/*"            { fn() { push-state(comment); start-chunked(); } }
<comment> @utf8unsafe     { fn() { unsafe-char("comment") } }
<comment> @commentchar    { fn() { extend-slice(id) } }
<comment> [\/\*]          { fn() { extend-slice(id) } }
<comment> .               { fn() { pop-state(); emit(LexError("illegal character in comment: " ++ end-chunked().show)) } }

--------------------------
-- line comments

<linecom> @utf8unsafe     { fn() { unsafe-char("line comment") } }
<linecom> @linechar       { fn() { extend-slice(id) } }
<linecom> @newline        { fn() { pop-state(); emit(LexComment(end-chunked().list.filter(fn(c) c !='\r').string)) } }
<linecom> .               { fn() { pop-state(); emit(LexError("illegal character in line comment: " ++ end-chunked().show)) } }

--------------------------
-- line directives (ignored for now)

<linedir> @utf8unsafe     { fn() { unsafe-char("line directive") } }
<linedir> @linechar       { fn() { extend-slice(id) } }
<linedir> @newline        { fn() { pop-state(); emit(LexComment(end-chunked().list.filter(fn(c) c !='\r').string)) } }
<linedir> .               { fn() { pop-state(); emit(LexError("illegal character in line directive: " ++ end-chunked().show)) } }

-- TODO: Add helper functions

{

fun extend-slice(f: sslice -> sslice)
  add-chunk(f(get-slice()))

fun pop-rawdelim()
  set-rawdelim(0)

fun push-rawdelim()
  set-rawdelim(get-slice().count)

fun get-name()
  get-string().new-name

fun get-qname()
  get-string().newQName

fun unsafe-char(kind: string)
  LexError("unsafe character in " ++ kind ++ ": " ++ get-string())
  end-chunked()
  pop-state()
  ()

fun newQName(s': string)
  val s = s'.list 
  val (rname, rsmod) = s.reverse.span(fn(c) { c != '/' })
  match rsmod // TODO: First case needs condition on rname == Nil
    Cons('/', Cons('/', rmod)) -> new-qualified(rmod.reverse.string, "/")
    Cons('/', rmod) -> new-qualified(rmod.reverse.string, rname.reverse.string)
    _ -> s.string.new-name

fun strip-parens(s: sslice)
  match s.string.list.reverse
    Cons(')', cs) -> 
      match cs.span(fn(c) { c != '(' })
        (op, Cons('(', qual)) -> (op ++ qual).reverse.string
        _ -> s.string
    _ -> s.string


// Reserved
val special-names = [ "{", "}"
    , "(", ")"
    , "<", ">"
    , "[", "]"
    , ";", ","
]

val reserved-names = 
      delay({
        string-pool().add-all(
        ["infix", "infixr", "infixl", "prefix", "postfix"
              , "type", "alias"
              , "struct", "enum", "con"
              , "val", "fun", "fn", "extern", "var"
              , "ctl", "final", "raw"
              , "if", "then", "else", "elif"
              , "return", "match", "with", "in"
              , "forall", "exists", "some"
              , "pub", "abstract"
              , "module", "import", "as"

              // effect handlers
              , "handler", "handle"
              , "effect", "receffect"
              , "named"
              , "mask"
              , "override"   

              // deprecated
              , "private", "public"  // use pub
              , "rawctl", "brk"      // use raw ctl, and final ctl

              // alternative names for backwards paper compatability
              , "control", "rcontrol", "except"
              , "ambient", "context" // use effcet
              , "inject"       // use mask
              , "use", "using" // use with instead
              , "function"     // use fun
              , "instance"     // use named

              // future reserved
              , "interface"
              , "unsafe"

              // operators
              , "="
              , "."
              , ":"
              , "->"
              , "<-"
              , ":="
              , "|"])
    })

fun is-reserved(name: string)
  reserved-names.force.is-interned(name)

fun is-prefix-op(name: string)
  name == "!" || name == "~"

fun string/is-malformed(name: string)
  name.list.charlist/is-malformed

fun charlist/is-malformed(name: list<char>)
  match name
    Cons('-', Cons(c, cs)) -> !c.is-alpha || cs.is-malformed
    Cons(c, Cons('-', cs)) -> !c.is-alpha || c.is-digit || cs.is-malformed
    Cons(_, cs) -> cs.is-malformed
    Nil -> False

val message-malformed
  = "malformed identifier: a dash must be preceded by a letter or digit, and followed by a letter"

fun char/from-char-esc(c)
  match c
    'n' -> '\n'
    'r' -> '\r'
    't' -> '\t'
    _ -> c

fun sslice/from-char-esc(s: sslice)
  s.drop(2).truncate().extend(1)

fun char/from-hex-esc(s: sslice)
  '\n' // TODO: Implement from-hex-esc

fun sslice/from-hex-esc(s: sslice)
  s.drop(3).extend(-1)

}
import compiler/syntax/layout
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/lib/pprint

effect format-eff
  fun indentation(): int

fun is-top()
  indentation() == 0

fun format(lexes: list<lexeme>)
  lexes

fun list/pretty(l: list<lexeme>)
  match l
    Cons(lex, ls) ->
      lex.pretty |.| ls.pretty

fun lex/pretty(lex: lexeme): div doc
  lex.pretty


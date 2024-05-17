import analysis/cps/sexpr
import std/data/linearset

type capture
  Empty
  One(s: sexpr)
  Many(i: int, v: list<capture>)

value struct syntaxRule
  pattern: sexpr
  tempalte: sexpr

value struct matcher
  literals: linearSet<string>

value struct syntaxRules
  rules: list<syntaxRule>
  literals: linearSet<string>


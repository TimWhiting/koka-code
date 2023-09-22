import std/os/path
import compiler/common/parse
import compiler/syntax/lexeme
import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/syntax/syntax
import compiler/common/name-prim
import compiler/kind/synonyms
import compiler/kind/importmap
import compiler/type/type
import core

fun parseCore(fname: path)
  lexParse(False, fn(lexes) lexes.allowDotIds.requalify, pProgram, fname.string, read-text-file(fname))

fun requalify(lexes: list<lexeme>): div list<lexeme>
  match lexes
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexId(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(mod.showPlain), name))), lexx))
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexIdOp(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(mod.showPlain), name))), lexx))
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexOp(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(mod.showPlain), name))), lexx))
    Cons(Lexeme(r1, LexId(mod)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexCons(name)), lexx)))  | slash.nameId  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexCons(qualify(newName(mod.showPlain), name))), lexx))
    Cons(lex, lexx)
      -> Cons(lex, requalify(lexx))
    [] -> []

fun allowDotIds(lexes: list<lexeme>): div list<lexeme>
  match lexes
    // Identifier
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexId(name)), lexx)) -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(prepend(".", name))), lexx))
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexWildCard(name)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2),  LexWildCard (".".prepend(name))), lexx))
    Cons(Lexeme(r1, LexId(name)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId (postpend("." ++ i.show, name))), lexx))
    // operator
    Cons(Lexeme(r1, LexKeyword(".")),Cons(Lexeme(r2, LexOp(name)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(".".prepend(name))), lexx))
    Cons(Lexeme(r1, LexOp(name)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId(postpend("." ++ i.show, name))), lexx))

    // constructor
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexCons(name)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexCons(".".prepend(name))), lexx))
    Cons(Lexeme(r1, LexCons(name)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexCons(postpend("." ++ i.show, name))), lexx))

    // (-.4), (++.2)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(name)), Cons(Lexeme(_,LexInt(i)),Cons(Lexeme(r5,LexSpecial(")")), lexx)))) // | last (nameId name) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(postpend(i.show, name))), lexx))
    // (/.4)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(name)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r5, LexSpecial(")")), lexx))))) // | last (nameId name) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(postpend("." ++ i.show, name))), lexx))
    // ([].1)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")),Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(_, LexKeyword(".")),Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r2, LexSpecial(")")), lexx))))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(postpend("." ++ i.show, "[]".newName))), lexx))
    // ([])
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")), Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(r2, LexSpecial(")")), lexx))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId("[]".newName)), lexx))
    Cons(l, lx) -> Cons(l, allowDotIds(lx))
    Nil -> Nil

fun pProgram()
  pmany("semis", pSemicolon)
  val (prog, env, inlines) = pModule()
  peof()
  (prog, pInlines(prog, source, env, inlines))

fun pModule()
  val (rng, doc) = pDocKeyword("module")
  pKeyword("interface")
  val (name, _) = pModulePath()
  pmany("semis", pSemicolon)
  braced
    val (imps, impAliases) = semis("", pImportDecl).unzip
    ()

fun pImportDecl(): <ast> (compiler/core/core/kimport, (name, name))
  unimplemented()


effect eenv
  fun setEnv(e: env): ()
  fun getEnv(): env;

struct env
  bound: name-map<typeVar>
  modName: name
  imports: importmap
  unique: int
  gamma: gamma
  locals: name-map<ktype>

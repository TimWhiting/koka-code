import compiler/syntax/koka-lex
import compiler/syntax/lexeme
import compiler/syntax/lex-help
import compiler/common/range
import std/os/file
import std/os/path

fun lexer(path: string, line: int, input: string): <pure> list<lexeme>
  lexing(Source(path, input), line, input)

fun lexing(source: source, line: int, input: string)
  val init-pos = Pos(source, 0, 0, 1)
  val state = State(init-pos, init-pos, [0], [], '\n', input.slice, LexWhite(""), "\"")
  with val alextrace = False
  go(state)

fun go(st0: state)
  match alexScan(st0, st0.states.head.unjust)
    AlexToken(st1,_,p) ->
      val idx0 = st0.current.count
      val idx1 = st1.current.count
      val bs = st0.current.subslice(0, idx0 - idx1)
      val p0 = st1.pos.pos-moves8(bs)
      val (token,st2) = p(bs)(st0)(st1(pos=p0))
      match token
        Nothing -> go(st2)
        Just(lex) -> 
          val rng = make-range(st0.startPos, st2.pos.pos/before)
          // trace(lex.show)
          Cons(Lexeme(rng, lex), go(st2(startPos=st2.pos, previousLex=lex)))
    AlexEOF -> []
    AlexSkip -> throw("Skip")
    AlexError -> throw("Error")

fun main()
  var done := False
  var s := read-text-file("compiler/core/core.kk".path)
  val source = Source("compiler/core/core.kk", s)
  lexing(source, 1, s)
  ()
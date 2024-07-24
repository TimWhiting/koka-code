import compiler/syntax/koka-lex
import compiler/syntax/lexeme
import compiler/syntax/lex-help
import compiler/common/range
import std/os/file
import std/os/path

fun lexing(st0: state)
  match alexScan(st0, st0.states.head.unjust)
    AlexToken(st1,_,p) ->
      val idx0 = st0.current.count
      val idx1 = st1.current.count
      val bs = st0.current.subslice(0, idx0 - idx1)
      val p0 = st1.pos.pos-moves8(bs)
      val (token,st2) = p(bs)(st0)(st1(pos=p0))
      match token
        Nothing -> lexing(st2)
        Just(lex) -> 
          val rng = make-range(st0.startPos, st2.pos.pos/before)
          println(lex)
          Cons(Lexeme(rng, lex), lexing(st2(startPos=st2.pos, previousLex=lex)))
    AlexEOF -> []
    AlexSkip -> throw("Skip")
    AlexError -> throw("Error")

fun main()
  var done := False
  var s := read-text-file("compiler/syntax/lex-test.kk".path)
  val source = Source("compiler/syntax/lex-test.kk", s)
  val init-pos = Pos(source, 0, 0, 1)
  val state = State(init-pos, init-pos, [0], [], '\n', s.slice, LexWhite(""), "\"")
  with val alextrace = False
  lexing(state)
  ()
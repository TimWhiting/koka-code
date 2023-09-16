import compiler/syntax/syntax
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim

fun main()
  val s = Source("name.kk", "Contents")
  val pos = Pos(s, 0, 0, 0)
  val p = PatLit(LitFloat(10.0, Range(pos, pos)))
  match p
    PatLit(v) -> v.show.println
    _ -> "Not Found".println
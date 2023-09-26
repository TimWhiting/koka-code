import compiler/core/parse
import compiler/core/core
import std/os/path
import compiler/common/range
import compiler/common/parse
import compiler/platform/config

fun main()
  val f = ".koka/v2.4.3/clang-debug/compiler_common_failure.kki"
  // val f = ".koka/v2.4.3/gcc-debug/compiler_common_failure.kki"
  with handler
    final ctl astError(msg: string, rng: range)
      println("error parsing ast at " ++ rng.showFullRange ++ "\n" ++ msg)
  val res = parseCore(f.path)
  res.fst.show.println
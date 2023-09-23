import compiler/core/parse

fun main()
  val f = ".koka/v2.4.3/clang-debug/compiler_common_failure.kki"
  val res = parseCore(f)
  res.show.println
import compiler/core/core
import compiler/common/syntax
import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/core/corevar
import compiler/core/borrowed
import compiler/type/type
import compiler/type/typevar
import compiler/kind/kind
import compiler/kind/newtypes

val debug = False

val externalNames = [(exprTrue.name, "true"), (exprFalse.name, "false")]
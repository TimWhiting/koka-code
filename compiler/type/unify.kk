import compiler/lib/pprint
import compiler/common/range
import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/unify
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/type/pretty
import compiler/type/operations
import compiler/core/core


effect unify
  final ctl unifyError(e: unifyErr): a
  fun extendSub(tv: typeVar, t: ktype): ()
  fun getSubst(): sub

fun withErr(e: unifyErr -> unifyErr, f: () -> <unify|e> a): <unify|e> a
  with override
    final ctl unifyError(er) e(er)
    fun extendSub(tv, t) extendSub(tv, t)
    fun getSubst() getSubst() 
  f()

fun subst(x: ktype): ktype
  getSubst() |-> x

type unifyErr
  NoMatch
  NoMatchKind
  NoMatchPred
  NoMatchSkolem(k: kind)
  NoMatchEffect(e1: ktype, e2: ktype)
  NoSubsume
  NoEntail
  Infinite
  NoArgMatch(i1: int, i2: int)

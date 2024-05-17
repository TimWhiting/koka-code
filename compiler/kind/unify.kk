import compiler/lib/pprint
import compiler/common/name
import compiler/common/range
import compiler/common/message
import compiler/common/color-scheme
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/infer-kind
import compiler/kind/infer-effect
import std/data/linearset

// Unify
type unifyContext
  Check(s: string, r: range)
  Infer(r: range)

effect unifyContextEff
  val uctx: unifyContext

fun kunify(rng: range, k1: infKind, k2: infKind)
  val sk1 = subst(k1)
  val sk2 = subst(k2)
  match mgu(sk1, sk2)
    UnifyKindOk(sub') -> extendKsub(sub')
    err ->
      kindError(rng, err, sk1, sk2)

fun kindError(rng: range, err: unify, k1: infKind, k2: infKind)
  val message = match err
    InfiniteKind -> "Invalid type (due to an infinite kind)"
    _ -> "Invalid type"
  val inferExtra =
    if k1.isInfKindScope || k2.isInfKindScope then
      [("hint".text, "scoped effects need a first type parameter annoted with kind \"::S\"".text)]
    else
      []
  val (rangeContext, expected, extra) =
    match uctx
      Check(msg, range) -> (range, "expected kind", [("because".text, msg.text)])
      Infer(range) -> (range, "expected kind", inferExtra)
  val [niceKind1, niceKind2] = niceInfKinds([k1, k2])
  addError(message.text |-| 
    table([
      ("type context".text, docFromRange(rangeContext)),
      ("type".text, docFromRange(rng)),
      ("inferred kind".text, niceKind2),
      (expected.text, niceKind1)
  ] ++ extra), rng)


// MGU
value type unify
  UnifyKindOk(ksub: ksub)
  InfiniteKind
  NoMatch

fun mgu(k1': infKind, k2': infKind)
  match (k1', k2')
    // Constants
    (KIVar(id1), KIVar(id2)) | id1 == id2 -> UnifyKindOk(ksubEmpty)
    (KICon(k1), KICon(k2)) -> 
      if matchKind(k1, k2) then UnifyKindOk(ksubEmpty) else NoMatch
    (KIApp(k1, k2), KIApp(l1, l2)) ->
      match mgu(k1, l1)
        UnifyKindOk(sub1) ->
          match mgu(sub1 |-> k2, sub1 |-> l2)
            UnifyKindOk(sub2) -> UnifyKindOk(sub2 |-> sub1)
            err -> err
        err -> err
    // pull up KApp's
    (KICon(KApp(k1, k2)), KIApp(l1, l2)) ->
      mgu(KIApp(KICon(k1), KICon(k2)), KIApp(l1, l2))
    (KIApp(k1, k2), KICon(KApp(l1, l2))) ->
      mgu(KIApp(k1, k2), KIApp(KICon(l1), KICon(l2)))
    // unify variables
    (KIVar(id), k) -> unifyVar(id, k)
    (k, KIVar(id)) -> unifyVar(id, k)
    _ -> NoMatch

fun unifyVar(id: int, k: infKind)
  if k.fkv.member(id) then InfiniteKind else UnifyKindOk(ksubSingle(id, k))

fun matchKind(k1': kind, k2': kind)
  match (k1', k2')
    (KCon(c1), KCon(c2)) -> c1 == c2
    (KApp(k1, k2), KApp(l1, l2)) -> matchKind(k1, l1) && matchKind(k2, l2)
    _ -> False
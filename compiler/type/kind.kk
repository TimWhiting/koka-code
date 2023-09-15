import compiler/type/type
import compiler/kind/kind
import compiler/common/name
import compiler/common/name-prim

fun effectIsAffine(eff: keffect)
  val (labs, tl) = eff.extractOrderedEffect
  tl.isEffectEmpty && labs.all(labelIsAffine)

fun labelIsLinear(eff: keffect)
  match eff.expandSyn
    TApp(TCon(tc), [_]) | tc.name == nameTpHandled1 -> True
    TApp(TCon(tc), [_]) | !(tc.name == nameTpHandled) ->
      val k = eff.kind // Allow alloc<global> etc
      k == kindLabel || k == kindEffect
    TCon(tc as TypeCon(_)) -> 
      val k = tc.kind // Builtin? too liberal? does not include exn
      k == kindLabel || k == kindEffect
    _ -> False

fun labelIsAffine(eff: keffect): exn bool
  match eff.expandSyn
    TApp(TCon(tc), [_]) | tc.name == nameTpHandled1 -> True
    // Allow exn
    TApp(TCon(tc), [TCon(tcx)]) | tc.name == nameTpHandled && tcx.name == nameTpPartial -> True
    TApp(TCon(tc), [_]) | !(tc.name == nameTpHandled) ->
      val k = eff.kind // Allow alloc<global> etc
      k == kindLabel || k == kindEffect
    TCon -> True // Builtin effects
    _ -> False

fun extractHandledEffect(eff: ktype): pure (list<ktype>, tau)
  val (ls, tl) = eff.extractOrderedEffect
  (ls.filter(isHandledEffect), tl)

fun handledToLabel(e: ktype): exn ktype
  if e.kind == kindHandled1 then TApp(tconHandled1, [e]) else TApp(tconHandled, [e])

fun containsHandledEffect(exclude: list<name>, eff: keffect): pure bool
  val (ls,_) = eff.extractEffectExtend
  ls.any(fn(e) e.getHandledEffect(exclude).is-just)

type handledSort
  ResumeOnce
  ResumeMany

fun isHandledEffect(tp: ktype)
  match tp.expandSyn
    TApp(TCon(TypeCon(name)), [_]) -> name == nameTpHandled || name == nameTpHandled1
    _ -> False

fun getHandledEffect(tp: ktype, exclude: list<name>): pure maybe<(handledSort, name)>
  match tp.expandSyn
    TApp(TCon(TypeCon(name)), [t])
      | name == nameTpHandled -> getHandledEffect(t, exclude)
      | name == nameTpHandled1 -> getHandledEffect(t, exclude)
    TApp(TCon(TypeCon(hxName)))
      -> if tp.kind == kindHandled && exclude.find(fn(t) t == hxName).is-nothing then Just((ResumeMany, hxName))
         elif tp.kind == kindHandled1 && exclude.find(fn(t) t == hxName).is-nothing then Just((ResumeOnce, hxName))
         elif hxName == nameTpScope && exclude.find(fn(t) t == hxName).is-nothing then Just((ResumeMany, hxName))
         else Nothing
    TCon(TypeCon(hxName, kind))
      | kind == kindHandled && exclude.find(fn(t) t == hxName).is-nothing -> Just((ResumeMany, hxName))
      | kind == kindHandled1 && exclude.find(fn(t) t == hxName).is-nothing -> Just((ResumeOnce, hxName))
    _ -> Nothing

fun kind(tp: ktype): exn kind
  match tp
    TForAll(_, _, t) -> t.kind
    TFun -> kindStar
    TVar(v) -> v.kind
    TCon(c) -> c.kind
    TSyn(syn, xs) -> kindApply(xs, syn.kind)
    TApp(tp, args) -> kindApply(args, tp.kind)

fun kindApply(tps: list<ktype>, k: kind): exn kind
  match (tps, k)
    ([], _) -> k
    (Cons(_, rest), KApp(KApp, k2)) -> kindApply(rest.unsafe-decreasing, k2)
    _ -> throw("type/kind kindApply: illegal kind in application")

  
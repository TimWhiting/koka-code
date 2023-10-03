import compiler/core/core
import compiler/lib/pprint
import compiler/type/type
import compiler/type/pretty
import compiler/common/name
import compiler/common/name-prim
import compiler/backend/c/helpers
import compiler/backend/c/dup-drops
import compiler/common/failure
import compiler/platform/config
import compiler/common/syntax

// Externals
fun extractExtern(ex: expr)
  match ex
    TypeApp(Var(tname, InfoExternal(formats)), _) -> Just((tname, formats))
    Var(tname, InfoExternal(formats)) -> Just((tname, formats))
    _ -> Nothing

// inlined external sometimes needs wrapping in an applied function block
fun genInlineExternal(tname: tName, formats: list<(target, string)>, args: list<doc>)
  val (decls, doc) = genExprExternal(tname, formats, args)
  if decls.is-nil then doc
  else fail("backend/c/from-core genInlineExternal: TODO: inline external declarations: " ++ show(vcat(decls ++ [doc])))

// generate external: needs to add try blocks for primitives that can throw exceptions

fun genExprExternal(tname: tName, formats: list<(target, string)>, args: list<doc>)
  val nm = tname.getName
  match args
    [argDoc] 
      | nm == nameBox || nm == nameUnbox ->
      // special case box / unbox
        val isBox = nm == nameBox
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, toTp) -> if isBox then fromTp else toTp
          _ -> fail("backend/c/from-core genExprExternal: box/unbox: expected function type")
        ([], if isBox then genBoxCall(tp, argDoc) else genUnboxCallOwned(tp, argDoc))
      // special case dup/drop
      | nm == nameDup || nm == nameDrop ->
        val isDup = nm == nameDup
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, _) -> fromTp
          _ -> fail("backend/c/from-core genExprExternal: dup/drop: expected function type")
        ([], hcat(genDupDropCall(isDup, tp, argDoc)))
      // special case is-unique
      | nm == nameIsUnique ->
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, _) -> fromTp
          _ -> fail("backend/c/from-core genExprExternal: isUnique: expected function type")
        ([], hcat(genIsUniqueCall(tp, argDoc)))
      // special case free
      | nm == nameFree ->
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, _) -> fromTp
          _ -> fail("backend/c/from-core genExprExternal: free: expected function type")
        ([], hcat(genFreeCall(tp, argDoc)))
      // special case decref
      | nm == nameDecRef ->
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, _) -> fromTp
          _ -> fail("backend/c/from-core genExprExternal: decRef: expected function type")
        ([], hcat(genDecRefCall(tp, argDoc)))
      // special case reuse
      | nm == nameReuse ->
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, _) -> fromTp
          _ -> fail("backend/c/from-core genExprExternal: reuse: expected function type")
        ([], hcat(genReuseCall(tp, argDoc)))
    [argDoc1, argDoc2]
      // special case dropn
      | nm == nameDrop ->
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, _) -> fromTp
          _ -> fail("backend/c/from-core genExprExternal: drop: expected function type")
        ([], hcat(genDropNCall(tp, [argDoc1, argDoc2])))
      // special case drop_reuse
      | nm == nameDropReuse ->
        val tp = match tname.typeOf
          TFun([(_, fromTp)], _, _) -> fromTp
          _ -> fail("backend/c/from-core genExprExternal: dropReuse: expected function type")
        ([], hcat(genDropReuseCall(tp, [argDoc1, argDoc2])))
    Nil
      // special case cfield hold
      | nm == nameCCtxHoleCreate ->  
        ([], genHoleCall(tname.typeOf.resultType))
  val format = getFormat(tname, formats)
  val argDocs = args.map(fn(d) if d.asString.list.all(fn(c) c.is-alpha || c.is-digit || c == '_') then d else d.parens)
  fun ppExternalF(name: name, k: list<char>): <compFlags,coreOptions,documentation,pure> doc
    match k
      Nil -> empty
      Cons('\\', Cons('#', xs)) -> char('#') |.| ppExternalF(name, xs)
      Cons('#', Cons('#', _)) -> fail("backend/c/from-core: type arguments in C external in " ++ tname.show)
      Cons('#', Cons(y, xs)) ->
        if y >= '1' && y <= '9' then
          val n = args.length
          val i = (y - '1').int
          if i >= args.length then
            fail("Illegal index in external: " ++ tname.show ++ ":" ++ tname.typeOf.pretty.show ++ "(" ++ k.string ++ "): index: " ++ i.show ++ ", arguments: " ++ args.show-list(show))
          args[i].unjust |.| ppExternalF(name, xs)
        else y.char |.| ppExternalF(name, xs)
      Cons(x, xs) -> char(x) |.| ppExternalF(name, xs)
  match format.lines.map(fn(fmt) ppExternalF(nm, fmt.list))    
    Nil -> ([], empty)
    ds -> (ds.init, ds.last.unjust)

fun getFormat(tname: tName, formats: list<(target, string)>)
  match formats.find(fn((t, _)) t == C(cTarget))
    Nothing -> 
      trace("warning: C backend does not support external in " ++ tname.show)
      "kk_unsuported_external(\"" ++ tname.show ++ "\")"
    Just(x) -> x.snd


  


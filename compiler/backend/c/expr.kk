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

fun genExpr(ex: expr): <compFlags,exn> (list<doc>, doc)
  fail("not implemented")

fun genExprs(l: list<expr>)
  val xs = l.map(genExpr)
  val (declss, docs) = xs.unzip
  (declss.concat, docs)


fun genAppNormal(f: expr, args: list<expr>)
  match (f, args)
    (Var(allocAt), [Var(at), App(Con(tname, repr), args)]) | allocAt.getName == nameAllocAt ->
      val (decls, argDocs) = args.genInlineableExprs
      val atDoc = at.getName.cppName
      (decls, conCreateName(tname.getName) |.| arguments([atDoc] ++ ppCtxPath(repr, tname, args.is-nil) ++ argDocs))
    (Var(allocAt), [Var(at), App(TypeApp(Con(tname, repr), targs), args)]) | allocAt.getName == nameAllocAt ->
      val (decls, argDocs) = args.genInlineableExprs
      val atDoc = at.getName.cppName
      (decls, conCreateName(tname.getName) |.| arguments([atDoc] ++ ppCtxPath(repr, tname, args.is-nil) ++ argDocs))
    (Var(allocAt), [at, Let(dgs, expr)]) | allocAt.getName == nameAllocAt -> // can happen due to box operations
      genExpr(Let(dgs, App(v, [at, expr])))
   
    // special: conAssignFields
    (Var(TName(conTagFieldsAssign, typeAssign)), Cons(reuseName, InfoConField(conName, conRepr, nameNil), Cons(Var(tag), fieldValues))) | conTagFieldAssign == nameConTagFieldsAssign ->
      val tmp = "con".genVarName
      val setTag = tmp |.| "->_base._block.header.tag = (kk_tag_t)".text |.| parens(tag.show.text) |.| semi
      val fieldNames = match typeAssign.splitFunScheme
        Just((_, _, args, _, _)) -> tail(tail(args.map(fst)))
        _ -> fail("backend/c/from-core: illegal conAssignFields type: " ++ typeAssign.pretty.show)
      val (decls, tmpDecl, assigns, result) = genAssignFields(tmp, conName, conRepr, reuseName, fieldNames, fieldValues)
      (decls ++ [tmpDelc, setTag] ++ assigns, result)
    (Var(TName(conFieldsAssign, typeAssign)), Cons(Var(reuseName, InfoConField(conName, conRepr, nameNil)), fieldValues)) | conFieldsAssign == nameConFieldsAssign ->
      val tmp = "con".genVarName
      val fieldNames = match typeAssign.splitFunScheme
        Just((_, _, args, _, _)) -> tail(args.map(fst))
        _ -> fail("backend/c/from-core: illegal conAssignFields type: " ++ typeAssign.pretty.show)
      val (decls, tmpDecl, assigns, result) = genAssignFields(tmp, conName, conRepr, reuseName, fieldNames, fieldValues)
      (decls ++ [tmpDelc] ++ assigns, result)
  
    // special: cfield-hole
    (Var(unbox), [App(Var(cfieldHole), [])]) | cfieldHole.getName == nameCCtxHoleCreate && unbox.getName == nameUnbox ->
      ([], genHoldCall(resultType, unbox.typeOf))
    
    // special: cfield-of
    (Var(cfieldOf), [App(Var(box), [App(Var(dup), [Var(c)])]), ELit(LitString(conName)), ELit(LitString(fieldName))]) | cfieldOf.getName == nameFieldAddrOf && dup.getName == nameDup ->
      val doc = genFieldAddress(c, conName.readQualified, fieldName.readQualified)
      ([], "(kk_box_t*)".text |.| parens(doc))
    (Var(cfieldOf), [App(Var(box), [Var(c)]), ELit(LitString(conName)), ELit(LitString(fieldName))]) | cfieldOf.getName == nameFieldAddrOf ->
      val drop = genDupDropCall(False, c.typeOf, c.getName.cppName).map(fn(x) x |.| semi)
      val doc = genFieldAddress(c, conName.readQualified, fieldName.readQualified)
      (drop, "(kk_box_t*)".text |.| parens(doc))
    
    // Add/sub small constant
    (Var(add), [arg, ELit(LitInt(i))]) | add.getName == nameIntAdd && i.isSmallInt -> // arg + i
      val (decls, argDocs) = genInlineableExprs([arg])
      (decls, "kk_integer_add_small_const".text |.| arguments(argDocs ++ [i.pretty]))
    (Var(add), [ELit(LitInt(i)), arg]) | add.getName == nameIntAdd && i.isSmallInt -> // i + arg
      val (decls, argDocs) = genInlineableExprs([arg])
      (decls, "kk_integer_add_small_const".text |.| arguments(argDocs ++ [i.pretty]))
    (Var(sub), [arg, ELit(LitInt(i))]) | sub.getName == nameIntSub && i.isSmallInt -> // arg - i
      val (decls, argDocs) = genInlineableExprs([arg])
      (decls, "kk_integer_add_small_const".text |.| arguments(argDocs ++ [(0 - i).pretty]))
    // normal
    _ ->
      val (decls, argDocs) = args.genInlineableExprs
      match f.extractExtern
        Just((tname, formats)) ->
          val (edecls, doc) = genExprExternal(tname, formats, argDocs)
          (edecls ++ decls, doc)
        _ ->
          match f
            // constructor
            Con(tname, repr) ->
              val at = (if repr.drepr.isValue || repr.is-conAsJust then [] else ["kk_reuse_null".text])
              (decls, conCreateName(tname.getName) |.| arguments(at ++ ppCtxPath(repr, tname, argDocs.is-nil) ++ argDocs))
            // call to known function
            Var(tname) | tname.getName == nameAllocAt ->
              fail("backend/c/genApp Var allocat" ++ f.show ++ " " ++ args.show-list(show))
            Var(tname, InfoArity(m, n)) | tname.getName.isQualified ->
              (decls, tname.getName.cppName |.| argument(argDocs))
            // call unknown function_t
            _ ->
              val (fdecls, fdoc) = match f
                Var(tname, info) -> ([], tname.getName.cppName)
                _ ->
                  val (fdecl, fname) = genVarBinding(f)
                  ([fdecl], fname.getName.cppName)
              val (cresTp, cargTps) = match f.typeOf.splitFunScheme
                Just((_, _, argTps, _, resTp)) ->
                  (resTp.cppType, tupled(["kk_function_t".text] ++ argTps.map(snd).map(cppType) ++ ["kk_context_t*".text]))
                _ ->
                  fail("backend/c/genAppNormal: expecting function type: " ++ f.typeOf.pretty.show)
              (fdecls ++ decls, "kk_function_call".text |.| arguments([cresTp, cargTps, fdoc, arguments(Cons(fdoc, argDocs))]))

fun ppCtxPath(crepr: conRepr, cname: tName, noArgs: bool)
  if noArgs then []
  else match crepr.ctxPath
    Just(CtxNone) -> ["0".text]
    Just(CtxField(fname)) -> ["kk_field_index_of".text |.| tupled(["struct".text |+| cname.getName.cppName, fname.getName.unqualify.cppName])]
    _ -> []

fun genAssignFields(tmp: doc, conName: tName, crepr: conRepr, reuseName: tName, fieldNames: list<name>, fieldValues: list<expr>)
  val (decls, fieldDocs) = fieldValues.genExprs
  val conTp = "struct".text |+| conName.getName.cppName |.| "*".text
  val tmpDecl = conTp |+| tmp |+| "=".text |+| parens(conTp) |.| reuseName.getName.cppName
  val assigns = zip(fieldNames, fieldDocs).map(fn((fname, fval)) tmp |.| "->".text |.| fname.cppName |+| "=".text |+| fval |.| semi)
  val ctxPath = match crepr.ctxPath
    Just(CtxField(fname)) -> ["kk_set_cpath".text |.| tupled(["struct".text |+| conName.getName.cppName, tmp, fname.getName.unqualify.cppName]) |.| semi]
    _ -> []
  val result = conBaseCastNameX(conName.getName) |.| arguments([tmp])
  (decls, tmpDecl, ctxPath ++ assigns, result)

fun genFieldAddress(conVar: tName, conName: tName, fieldName: name)
  parens("&".text |.| conAsNameX(conName.getName) |.| arguments([conVar.getName.cppName]) |.| "->".text |.| fieldName.unqualify.cppName)

fun genCCtxSetContextPath(conVar: tName, conName: name, fieldName: name)
  "kk_cctx_setcp".text |.| arguments([conVar.getName.cppName, "offsetof".text |.| tupled(["struct".text |+| conName.cppName, fieldName.unqualify.cppName])])

fun genAppSpecial(f: expr, args: list<expr>)
  fun default()
    match f.extractExtern
      Just((tname, _)) ->
        val nm = tname.getName
        match args
          [ELit(LitInt(i))] ->
            if nm == nameInt32 && i.isSmallInt32 then
              Just(genLitInt32(i))
            elif nm == nameInt64 && i.isSmallInt64 then
              Just(genLitInt64(i))
            elif nm == nameSSizeT && i.isSmallSSizeT then
              Just(genLitSSizeT(i))
            elif nm == nameIntPtrT && i.isSmallIntPtrT then
              Just(genLitIntPtrT(i))
            elif nm == nameByte && i.isSmallUInt8 then
              Just(genLitUint8(i))
            else
              Nothing
          _ -> Nothing
      _ -> Nothing
  match (f, args)
    (Var(tname), [ELit(LitInt(i))]) ->
      val nm = tname.getName
      if nm == nameInt32 && i.isSmallInt32 then
        return Just(genLitInt32(i))
      elif nm == nameInt64 && i.isSmallInt64 then
        return Just(genLitInt64(i))
      elif nm == nameSSizeT && i.isSmallSSizeT then
        return Just(genLitSSizeT(i))
      elif nm == nameIntPtrT && i.isSmallIntPtrT then
        return Just(genLitIntPtrT(i))
      elif nm == nameByte && i.isSmallUInt8 then
        return Just(genLitUint8(i))
      else default()
    _ -> default()  

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
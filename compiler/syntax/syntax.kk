import std/num/float64
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import newstd/data/linearset
import newstd/core

pub struct program<t, k>
  source: source
  name: name
  name-range: range
  typeDefs: list<typeDefGroup<t,k>>
  defs: defGroups<t>
  pub imports: imports
  externals: externals
  fixDefs: fixDefs
  doc: string

fun program/show(Program(_, n, _, typeDefs, defs, imports, externals, fixDefs, _):program<t,k>, ?t/show: (t) -> <div|e> string, ?k/show: (k) -> <div|e> string): <div|e> string
  n.name/name/show ++ ":\n" ++ "typeDefs " ++ typeDefs.list/show ++ "\n" ++ "defs " ++ defs.list/show ++ "\n" ++ 
  "imports " ++ imports.list/show ++ "\n" ++ "externals " ++ externals.list/show ++ "\n" ++ 
  "fixDefs " ++ fixDefs.list/show ++ "\n"
  
alias userProgram = program<userType, userKind>;
alias userExpr = expr<userType>;
alias userDef = def<userType>;
alias userDefGroup = defGroup<userType>;
alias userTypeDef = typeDef<userType, userType, userKind>;
alias userTypeDefGroup = typeDefGroup<userType, userKind>;
alias userUserCon = userCon<userType, userType, userKind>;
alias userPattern = pattern<userType>
alias userBranch = branch<userType>
alias userGuard = guard<userType>
alias userHandlerBranch = handlerBranch<userType>
alias userValueBinder = valueBinder<()>
alias userTypeBinder = typeBinder<userKind>

alias externals = list<external>;

type external
  External(name: name, t: userType, params: list<paramInfo>, name-range: range, range: range, inlineCall: list<(target, externalCall)>, vis: visibility, fipAnnot: fipT, doc: string)
  ExternalImport(eImport: list<(target,list<(string, string)>)>, range: range)

fun external/show(e: external): div string
  match e
    External(name, t, params, name-range, range, inlineCall, vis, fipAnnot, doc) -> 
      "External " ++ name.name/name/show ++ " " ++ t.show ++ " " ++ params.list/show ++ " " ++ name-range.show-full-range ++ " " ++ range.show-full-range ++ " " ++ 
      inlineCall.list/show ++ " " ++ vis.show ++ " " ++ fipAnnot.show ++ " " ++ doc.show
    ExternalImport(eImport, range) -> "ExternalImport " ++ eImport.list/show(?show=fn((t:target, l:list<(string,string)>)) t.show ++ " " ++ l.list/show) ++ " " ++ range.show-full-range

value type externalCall
  ExternalInline(content: string)
  ExternalCall(call: string)

fun externcall/show(e: externalCall): string
  match e
    ExternalInline(content) -> "ExternalInline " ++ content
    ExternalCall(call) -> "ExternalCall " ++ call

alias fixDefs = list<fixDef>;

struct fixDef
  name: name
  fixity: fixity
  range: range
  vis: visibility

fun fixdef/show(f: fixDef): string
  f.name.name/name/show ++ " " ++ f.fixity.show ++ " " ++ f.range.show-full-range ++ " " ++ f.vis.show

alias imports = list<kimport>;

struct kimport
  name: name
  fullName: name
  range: range
  vis: visibility

fun kimport/show(i: kimport): string
  i.name.name/name/show ++ " " ++ i.fullName.name/name/show ++ " " ++ i.range.show-full-range ++ " " ++ i.vis.show

alias typeDefGroups<t,k> = list<typeDefGroup<t,k>>;

value type typeDefGroup<t,k>
  TypeDefRec(defs: list<typeDef<t,t,k>>)
  TypeDefNonRec(tdef: typeDef<t,t,k>)

fun typedefgroup/show(t: typeDefGroup<t,k>, ?t/show: (t) -> <div|e> string, ?k/show: (k) -> <div|e> string): <div|e> string
  match t
    TypeDefRec(defs) -> "TypeDefRec " ++ defs.list/show
    TypeDefNonRec(d) -> "TypeDefNonRec " ++ d.show

type typeDef<t,u,k>
  Synonym(binder: typeBinder<k>, params: list<typeBinder<k>>, synonym: t, range: range, vis: visibility, doc: string)
  DataType(binder: typeBinder<k>, params: list<typeBinder<k>>, constrs: list<userCon<t,u,k>>, range: range, vis: visibility, sort: dataKind, ddef: dataDef, isExtend: bool, doc: string)

fun typedef/show(td: typeDef<t,u,k>, ?t/show: (t) -> <div|e> string, ?u/show: (u) -> <div|e> string, ?k/show: (k) -> <div|e> string): <div|e> string
  match td
    Synonym(binder, params, synonym, range, vis, doc) -> "Synonym " ++ binder.show ++ " " ++ params.list/show ++ " " ++ synonym.t/show ++ " " ++ range.show-full-range ++ " " ++ vis.show ++ " " ++ doc.show
    DataType(binder, params, constrs, range, vis, sort, ddef, isExtend, doc) -> 
      "DataType " ++ binder.show ++ " " ++ params.list/show ++ " " ++ constrs.list/show ++ " " ++ 
      range.show-full-range ++ " " ++ vis.show ++ " " ++ sort.show ++ " " ++ ddef.show ++ " " ++ isExtend.show ++ " " ++ doc.show

struct typeBinder<k>
  name: name
  kind: k
  name-range: range
  range: range;

fun tb/show(t: typeBinder<k>, ?show: (k) -> <div|e> string): <div|e> string
  t.name.name/name/show ++ " " ++ t.kind.show ++ " " ++ t.name-range.show-full-range ++ " " ++ t.range.show-full-range

struct userCon<t, u, k>
  name: name
  existentials: list<typeBinder<k>>
  params: list<(visibility, valueBinder<t, maybe<expr<u>>>)>
  result: maybe<t>
  name-range: range
  range: range
  vis: visibility
  doc: string  

fun con/show(u: userCon<t,u,k>, ?t/show: (t) -> <div|e1> string, ?u/show: (u) -> <div|e1> string, ?k/show: (k) -> <div|e1> string): <div|e1> string
  u.name.name/name/show ++ " " ++ u.existentials.list/show ++ " " ++ u.params.list/show ++ " " ++ u.result.show ++ " " ++ u.name-range.show-full-range ++ " " ++ u.range.show-full-range ++ " " ++ u.vis.show ++ " " ++ u.doc.show

alias defGroups<t> = list<defGroup<t>>;
  
type defGroup<t>
  DefRec(defs: list<def<t>>)
  DefNonRec(d: def<t>)

fun dg/show(d: defGroup<t>, ?show: (t) -> <div|e1> string): <div|e1> string
  match d
    DefRec(defs) -> "DefRec " ++ defs.list/show
    DefNonRec(d) -> "DefNonRec " ++ d.show

alias defs<t> = list<def<t>>;

struct valueBinder<t, e>
  name: name
  binderType: t // Always present for constructors
  expr: e // always present for definitions as 'Expr t'
                // Function and constructor parameters use 'Maybe (Expr t)' for default values.
                // Pattern bindings ('PatVar') use unit '()'.
  name-range: range
  range: range; // full range

fun vb/show(v: valueBinder<t,e>, ?t/show: (t) -> <div|e1> string, ?e/show: (e) -> <div|e1> string): <div|e1> string
  v.name.name/name/show ++ " " ++ v.binderType.t/show ++ " " ++ v.expr.e/show ++ " " ++ v.name-range.show-full-range ++ " " ++ v.range.show-full-range

struct def<t>
  binder: valueBinder<(), expr<t>>
  range: range
  visibilty: visibility
  sort: defSort
  defInline: defInline
  doc: string;

fun def/show(d: def<t>, ?show: (t) -> <div|e> string): <div|e> string
  d.binder.show ++ " " ++ d.range.show-full-range ++ " " ++ d.visibilty.show ++ " " ++ d.sort.show ++ " " ++ d.defInline.show ++ " " ++ d.doc

fun defIsVal(d: def<t>): bool
  !d.sort.is-fun

val guardTrue = Var(nameTrue, False, range/null)

type expr<t>
  Lam(binder: list<valueBinder<maybe<t>,maybe<expr<t>>>>, e: expr<t>, range: range)
  Let(d: defGroup<t>, e: expr<t>, range: range)
  Bind(d: def<t>, e: expr<t>, range: range)
  App(e: expr<t>, args: list<(maybe<(name, range)>, expr<t>)>, range: range)
  Var(name: name, isOp: bool, range: range)
  Literal(l: lit, range: range = l.range)
  Ann(e: expr<t>, t: t, range: range)
  Case(e: expr<t>, cases: list<branch<t>>, range: range)
  Parens(e: expr<t>, name: name, range: range)
  Inject(t: t, e: expr<t>, behind: bool, range: range)
  Handler(sort: handlerSort, scope: handlerScope, hOverride: handlerOverride, allowMask: maybe<bool>, hEffect: maybe<t>, localPars: list<valueBinder<maybe<t>, ()>>, initially: maybe<expr<t>>, hReturn: maybe<expr<t>>, finally: maybe<expr<t>>, branches: list<handlerBranch<t>>, declRange: range, range: range)

// fun expr/show(expr: expr<t>): string
//   ""

fun expr/show(expr: expr<t>, ?show: (t) -> <div|e1> string): <div|e1> string
  match expr
    // Lam(binder, e, rng) -> "Lam " ++ binder.list/show ++ " " ++ e.show ++ " " ++ rng.show-full-range
    // Let(d, e, rng) -> "Let " ++ d.dg/show ++  " " ++ e.expr/show ++ " " ++ rng.show-full-range 
    // Bind(d, e, rng) -> "Bind " ++ d.show ++ " " ++ e.show ++ " " ++ rng.show-full-range
    // App(e, args, rng) -> "App " ++ e.show ++ " " ++ args.list/show(?show=fn((mn, e')) mn.show(?show=fn((n,_)) n.name/name/show) ++ "=" ++ expr/show(e')) ++ " " ++ rng.show-full-range
    Var(n, isOp, rng) -> "Var " ++ n.name/name/show ++ " " ++ isOp.show ++ " " ++ rng.show-full-range
    Literal(l) -> "Literal " ++ l.show
    Ann(e, t, rng) -> "Ann " ++ e.show ++ " " ++ t.show ++ " " ++ rng.show-full-range
    // Case(e, cases, rng) -> "Case " ++ e.show ++ " " ++ cases.list/show ++ " " ++ rng.show-full-range
    Parens(e, n, rng) -> "Parens " ++ e.show ++ " " ++ n.name/name/show ++ " " ++ rng.show-full-range
    // Inject(t, e, behind, rng) -> "Inject " ++ t.show ++ " " ++ e.show ++ " " ++ behind.show ++ " " ++ rng.show-full-range
    _ -> ""
    // Handler(sort, scope, hOverride, allowMask, hEffect, localPars, initially, hReturn, fin, branches, declRange, rng) -> 
      // "Handler " ++ sort.show ++ " " ++ scope.show ++ " " ++ hOverride.show ++ " " ++ 
      // allowMask.show ++ " " ++ hEffect.show ++ " " ++ localPars.list/show ++ " " ++ 
      // initially.show ++ " " ++ hReturn.show ++ " " ++ fin.show ++ " " ++
      // branches.list/show ++ " " ++ declRange.show-full-range ++ " " ++ rng.show-full-range

type handlerOverride
  HandlerOverride
  HandlerNoOverride

fun hov/show(h: handlerOverride): string
  match h
    HandlerOverride -> "HandlerOverride"
    HandlerNoOverride -> "HandlerNoOverride"

type handlerScope
  HandlerScoped
  HandlerNoScope

fun hs/show(h: handlerScope): string
  match h
    HandlerScoped -> "HandlerScoped"
    HandlerNoScope -> "HandlerNoScope"

struct handlerBranch<t>
  branchName: name
  branchPars: list<valueBinder<maybe<t>, ()>>
  branchExpr: expr<t>
  branchSort: operationSort
  branchNameRange: range
  branchPatRange: range

fun hb/show(h: handlerBranch<t>, ?show: (t) -> <div|e> string): <div|e> string
  h.branchName.name/name/show ++ " " ++ h.branchPars.list/show ++ " " ++ h.branchExpr.show ++ " " ++
  h.branchSort.show ++ " " ++ h.branchNameRange.show-full-range ++ " " ++ h.branchPatRange.show-full-range
  
struct branch<t>
  branchPattern: pattern<t>
  branchGuard: list<guard<t>>

fun branch/show(b: branch<t>, ?show: (t) -> <div|e> string): <div|e> string
  b.branchPattern.show ++ " " ++ b.branchGuard.list/show
  
struct guard<t>
  guardTest: expr<t>
  guardExpr: expr<t>

fun guard/show(g: guard<t>, ?show: (t) -> <div|e> string): <div|e> string
  g.guardTest.show ++ " " ++ g.guardExpr.show

type pattern<t>
  PatWild(range: range)
  PatVar(patvar: valueBinder<maybe<t>, pattern<t>>, range: range= patvar.range)
  PatAnn(p: pattern<t>, t: t, range: range)
  PatCon(name: name, args: list<(maybe<(name, range)>, pattern<t>)>, nameRange: range, range: range)
  PatParens(p: pattern<t>, range: range)
  PatLit(value: lit, range:range = value.range)

fun pat/show(p: pattern<t>, ?show: (t) -> <div|e> string): <div|e> string
  match p
    PatWild(range) -> "PatWild " ++ range.show-full-range
    // PatVar(patvar) -> "PatVar " ++ patvar.show
    // PatAnn(p, t, range) -> "PatAnn " ++ p.show ++ " " ++ t.show ++ " " ++ range.show-full-range
    // PatCon(name, args, nr, range) -> 
    //   "PatCon " ++ name.name/name/show ++ " " ++ // args.list/show(?show=fn((mn, p')) mn.show(?show=fn((n,_)) n.name/name/show) ++ p'.show) ++
    //   " " ++ nr.show-full-range ++ " " ++ range.show-full-range
    // PatParens(p, range) -> "PatParens " ++ p.show ++ " " ++ range.show-full-range
    // PatLit(value) -> "PatLit " ++ value.show
    _ -> ""

type lit
  LitInt(value: int, range: range)
  LitFloat(value: float64, range: range)
  LitChar(value: string, range: range)
  LitString(value: string, range: range)

fun lit/show(l: lit): string
  match l
    LitInt(v, r) -> v.show ++ " " ++ r.show-full-range
    LitFloat(v, r) -> v.show ++ " " ++ r.show-full-range
    LitChar(v, r) -> v ++ " " ++ r.show-full-range
    LitString(v, r) -> v ++ " " ++ r.show-full-range

// Types and kinds
alias kUserTypes<k> = list<kUserType<k>>

type userQuantifier
  QSome
  QForall
  QExists

fun uquant/show(u: userQuantifier): string
  match u
    QSome -> "QSome"
    QForall -> "QForall"
    QExists -> "QExists"

// Higher ranked types
type kUserType<k>
  TpQuan(q: userQuantifier, b: typeBinder<k>, kind: kUserType<k>, range: range)
  TpQual(l: list<kUserType<k>>, kind: kUserType<k>)
  TpFun(a: list<(name, kUserType<k>)>, b: kUserType<k>, c: kUserType<k>, range: range)
  TpApp(a: kUserType<k>, b: list<kUserType<k>>, range: range)
  TpVar(name: name, range: range)
  TpCon(name: name, range: range)
  TpParens(t: kUserType<k>, range: range)
  TpAnn(t: kUserType<k>, kind: k)

alias userType = kUserType<userKind>

fun ut/show(u: userType): div string
  match u
    TpQuan(q, b, kind, range) -> "TpQuan " ++ q.show ++ " " ++ b.show ++ " " ++ kind.show ++ " " ++ range.show-full-range
    TpQual(l, kind) -> "TpQual " ++ l.list/show ++ " " ++ kind.show
    TpFun(a, b, c, range) -> "TpFun " ++ a.list/show(?show=fn((n, ut)) n.name/name/show ++ ":" ++ ut.show) ++ " " ++ b.show ++ " " ++ c.show ++ " " ++ range.show-full-range
    TpApp(a, b, range) -> "TpApp " ++ a.show ++ " " ++ b.list/show ++ " " ++ range.show-full-range
    TpVar(n, range) -> "TpVar " ++ n.name/name/show ++ " " ++ range.show-full-range
    TpCon(n, range) -> "TpCon " ++ n.name/name/show ++ " " ++ range.show-full-range
    TpParens(t, range) -> "TpParens " ++ t.show ++ " " ++ range.show-full-range
    TpAnn(t, kind) -> "TpAnn " ++ t.show ++ " " ++ kind.show

type userKind
  KindCon(name: name, range: range)
  KindArrow(from: userKind, to: userKind)
  KindParens(kind: userKind, range: range)
  KindNone // Flags no explicit kind annotation

fun uk/show(u: userKind): string
  match u
    KindCon(name, range) -> "KindCon " ++ name.name/name/show ++ " " ++ range.show-full-range
    KindArrow(from, to) -> "KindArrow " ++ from.show ++ " " ++ to.show
    KindParens(kind, range) -> "KindParens " ++ kind.show ++ " " ++ range.show-full-range
    KindNone -> "KindNone"



// Range

fun kut/range(tp: kUserType<k>, rK: (k) -> range): range
  match tp
    TpQuan(range=range) -> range
    TpQual(preds, tp) -> Range(preds.head.default(tp).unsafe-decreasing.range(rK).start, tp.range(rK).end)
    TpFun(range=range) -> range
    TpApp(range=range) -> range
    TpVar(range=range) -> range
    TpCon(range=range) -> range
    TpParens(range=range) -> range
    TpAnn(userTp, kind) -> Range(userTp.range(rK).start, kind.rK.end)

fun uk/range(uk: userKind): range
  match uk
    KindCon(range=range) -> range
    KindArrow(k1, k2) -> Range(k1.range.start, k2.range.end)
    KindParens(range=range) -> range
    KindNone -> range/null

fun ut/range(utp: userType): range
  utp.range(range)

fun uhb/range(uhb: userHandlerBranch): range
  uhb.branchPatRange.combine(uhb.branchExpr.range)

// free type variables
fun maybe/free-type-vars(m: maybe<a>, f: (a) -> div nameSet): div nameSet
  match m
    Nothing -> names/empty
    Just(x) -> f(x)

fun list/free-type-vars(l: list<a>, f: (a) -> div nameSet): div nameSet
  l.foldl(names/empty, fn(s:nameSet, x) s + f(x))

fun kut/free-type-vars(tp: kUserType<k>): div nameSet
  match tp
    TpQuan(_, TypeBinder(name), tp, _) -> tp.free-type-vars - name
    TpQual(preds, tp) -> free-type-vars(Cons(tp, preds), free-type-vars)
    TpFun(args, eff, tp) -> free-type-vars(Cons(tp,Cons(eff,args.map(snd))), free-type-vars)
    TpApp(tp, args) -> tp.free-type-vars + args.free-type-vars(free-type-vars)
    TpVar(name) -> names/empty.add(name)
    TpCon -> names/empty
    TpParens(tp) -> tp.free-type-vars
    TpAnn(tp) -> tp.free-type-vars

// access definitions
fun def/body(d: def<t>): expr<t>
  d.binder.expr

fun def/name(d: def<t>): name
  d.binder.name

fun def/type(d: def<t>): maybe<t>
  match d.binder.expr
    Ann(_, tp) -> Just(tp)
    _ -> Nothing

fun typedef/name(d: typeDef<t,u,k>): name
  d.binder.name

fun typdef/name-range(d: typeDef<t,u,k>): range
  d.binder.name-range

fun program/null(n: name)
  Program(source/null, n, range/null, [], [], [preludeImport], [], [], "")

// Import declaration for the standard prelude
val preludeImport = Kimport(nameSystemCore, nameSystemCore, range/null, Private)

fun make-program(n: name, tdefs: list<typeDef<t,t,k>>, defs: list<def<t>>): program<t,k>
  Program(source/null, n, range/null, [TypeDefRec(tdefs)], [DefRec(defs)], [], [], [], "")

fun add-imports(p: program<t,k>, imps: list<kimport>): program<t,k>
  Program(p.source, p.name, p.name-range, p.typeDefs, p.defs, imps ++ p.imports, p.externals, p.fixDefs, p.doc)

fun remove-tdefs(tdefs: list<typeDef<t,t,k>>, tdefs0: list<typeDef<t,t,k>>): list<typeDef<t,t,k>>
  tdefs0.foldl(tdefs, fn(acc, tdef) acc.filter(fn(tdef') tdef'.name != tdef.name))

fun remove-defs(defs: list<def<k>>, defs0: list<def<k>>): list<def<k>>
  defs0.foldl(defs, fn(acc, def) acc.filter(fn(def') def'.name != def.name))

fun add-defs(p: program<t,k>, tdefs0: list<typeDef<t,t,k>>, defs0: list<def<t>>): <exn,comp-flags> program<t,k>
  val tdefs' = match p.typeDefs
    [] -> [TypeDefRec(tdefs0)]
    [TypeDefRec(ts)] -> [TypeDefRec(ts.remove-tdefs(tdefs0) ++ tdefs0)]
    _ -> fail("syntax/syntax: can not add type definitions to processed tree")
  val defs' = match p.defs
    [] -> [DefRec(defs0)]
    [DefRec(ds)] -> [DefRec(ds.remove-defs(defs0) ++ defs0)]
    _ -> fail("syntax/syntax: can not add definitions to processed tree")
  Program(p.source, p.name, p.name-range, tdefs', defs', p.imports, p.externals, p.fixDefs, p.doc)

fun remove-all-defs(p: program<t,k>): program<t,k>
  p(defs=[])

fun program-remove-def(p: program<t,k>, nm: name): program<t,k>
  fun filter-tdef(tdefg: typeDefGroup<t,k>): typeDefGroup<t,k>
    match tdefg
      TypeDefRec(tdefs) -> TypeDefRec(tdefs.filter(fn(tdef) tdef.name != nm))
      TypeDefNonRec(tdef) -> TypeDefNonRec(tdef)
  fun filterDef(defg: defGroup<t>): defGroup<t>
    match defg
      DefRec(defs) -> DefRec(defs.filter(fn(def) def.name != nm))
      DefNonRec(def) -> DefNonRec(def)
  Program(p.source, p.name, p.name-range, p.typeDefs.map(filter-tdef), p.defs.map(filterDef), p.imports, p.externals, p.fixDefs, p.doc)

fun program-find(p: program<t,k>, nm: name): maybe<range>
  fun trange(tdefg: typeDefGroup<t,k>): list<(name, range)>
    match tdefg
      TypeDefRec(tdefs) -> tdefs.map(fn(tdef) (tdef.name, tdef.name-range))
      TypeDefNonRec(tdef) -> [(tdef.name, tdef.name-range)]
  fun drange(defg: defGroup<t>): list<(name, range)>
    match defg
      DefRec(defs) -> defs.map(fn(def) (def.name, def.range))
      DefNonRec(def) -> [(def.name, def.range)]
  val names = p.typeDefs.map(trange).concat ++ p.defs.map(drange).concat
  names.find(fn((n, _)) n == nm).map(snd)

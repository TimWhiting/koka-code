import std/num/float64
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import newstd/data/linearset
import newstd/core

pub struct program<t, k>
  source: source
  name: name
  nameRange: range
  typeDefs: list<typeDefGroup<t,k>>
  defs: defGroups<t>
  pub imports: imports
  externals: externals
  fixDefs: fixDefs
  doc: string


fun show(Program(_, n, _, typeDefs, defs, imports, externals, fixDefs, _):program<t,k>, showT: (t) -> div string, showK: (k) -> div string): div string
  name/show(n) ++ ":\n" ++ "typeDefs " ++ typeDefs.show-list(fn(t) t.show(showT, showK)) ++ "\n" ++ "defs " ++ defs.show-list(fn(d) d.show(showT)) ++ "\n" ++ 
  "imports " ++ imports.show-list(fn(i) i.show) ++ "\n" ++ "externals " ++ externals.show-list(fn(e) e.show) ++ "\n" ++ 
  "fixDefs " ++ fixDefs.show-list(fn(f) f.show) ++ "\n"

  
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
  External(name: name, t: userType, params: list<paramInfo>, nameRange: range, range: range, inlineCall: list<(target, externalCall)>, vis: visibility, fipAnnot: fipT, doc: string)
  ExternalImport(eImport: list<(target,list<(string, string)>)>, range: range)

fun show(e: external): div string
  match e
    External(name, t, params, nameRange, range, inlineCall, vis, fipAnnot, doc) -> 
      "External " ++ name.show ++ " " ++ t.show ++ " " ++ params.show-list(fn(p) p.show) ++ " " ++ nameRange.showFullRange ++ " " ++ range.showFullRange ++ " " ++ 
      inlineCall.show-list(fn(c) c.fst.show ++ " " ++ c.snd.show) ++ " " ++ vis.show ++ " " ++ fipAnnot.show ++ " " ++ doc.show
    ExternalImport(eImport, range) -> "ExternalImport " ++ eImport.show-list(fn(e') e'.fst.show ++ " " ++ e'.snd.show-list(fn(e1) e1.fst ++ " " ++ e1.snd)) ++ " " ++ range.showFullRange

value type externalCall
  ExternalInline(content: string)
  ExternalCall(call: string)

fun show(e: externalCall): string
  match e
    ExternalInline(content) -> "ExternalInline " ++ content
    ExternalCall(call) -> "ExternalCall " ++ call

alias fixDefs = list<fixDef>;

struct fixDef
  name: name
  fixity: fixity
  range: range
  vis: visibility

fun show(f: fixDef): string
  f.name.show ++ " " ++ f.fixity.show ++ " " ++ f.range.showFullRange ++ " " ++ f.vis.show

alias imports = list<kimport>;

struct kimport
  name: name
  fullName: name
  range: range
  vis: visibility

fun show(i: kimport): string
  i.name.show ++ " " ++ i.fullName.show ++ " " ++ i.range.showFullRange ++ " " ++ i.vis.show

alias typeDefGroups<t,k> = list<typeDefGroup<t,k>>;

value type typeDefGroup<t,k>
  TypeDefRec(defs: list<typeDef<t,t,k>>)
  TypeDefNonRec(def: typeDef<t,t,k>)

fun show(t: typeDefGroup<t,k>, showT: (t) -> div string, showK: (k) -> div string): div string
  match t
    TypeDefRec(defs) -> "TypeDefRec " ++ defs.show-list(fn(t') t'.show(showT, showT, showK))
    TypeDefNonRec(def) -> "TypeDefNonRec " ++ def.show(showT, showT, showK)

type typeDef<t,u,k>
  Synonym(binder: typeBinder<k>, params: list<typeBinder<k>>, synonym: t, range: range, vis: visibility, doc: string)
  DataType(binder: typeBinder<k>, params: list<typeBinder<k>>, constrs: list<userCon<t,u,k>>, range: range, vis: visibility, sort: dataKind, def: dataDef, isExtend: bool, doc: string)

fun show(td: typeDef<t,u,k>, showT: (t) -> div string, showU: (u) -> div string, showK: (k) -> div string): div string
  match td
    Synonym(binder, params, synonym, range, vis, doc) -> "Synonym " ++ binder.show(showK) ++ " " ++ params.show-list(fn(b) b.show(showK)) ++ " " ++ synonym.showT ++ " " ++ range.showFullRange ++ " " ++ vis.show ++ " " ++ doc.show
    DataType(binder, params, constrs, range, vis, sort, def, isExtend, doc) -> 
      "DataType " ++ binder.show(showK) ++ " " ++ 
      params.show-list(fn(b) b.show(fn(k) k.showK)) ++ " " ++ 
      constrs.show-list(fn(c) c.show(showT, showU, showK)) ++ " " ++ 
      range.showFullRange ++ " " ++ vis.show ++ " " ++ sort.show ++ " " ++ def.show ++ " " ++ isExtend.show ++ " " ++ doc.show

struct typeBinder<k>
  name: name
  kind: k
  nameRange: range
  range: range;

fun show(t: typeBinder<k>, showK: (k) -> e string): e string
  t.name.show ++ " " ++ t.kind.showK ++ " " ++ t.nameRange.showFullRange ++ " " ++ t.range.showFullRange

struct userCon<t, u, k>
  name: name
  existentials: list<typeBinder<k>>
  params: list<(visibility, valueBinder<t, maybe<expr<u>>>)>
  result: maybe<t>
  nameRange: range
  range: range
  vis: visibility
  doc: string  

fun show(u: userCon<t,u,k>, showT: (t) -> div string, showU: (u) -> div string, showK: (k) -> div string): div string
  u.name.show ++ " " ++ u.existentials.show-list(fn(e) e.show(showK)) ++ " " ++ u.params.show-list(fn(p) p.fst.show ++ "," ++ p.snd.show(fn(t) t.showT, fn(m) m.show(fn(e1) e1.show(showU)))) ++ " " ++ u.result.show(showT) ++ " " ++ u.nameRange.showFullRange ++ " " ++ u.range.showFullRange ++ " " ++ u.vis.show ++ " " ++ u.doc.show

alias defGroups<t> = list<defGroup<t>>;
  
type defGroup<t>
  DefRec(defs: list<def<t>>)
  DefNonRec(def: def<t>)

fun show(d: defGroup<t>, showT: (t) -> e string): e string
  match d
    DefRec(defs) -> "DefRec " ++ defs.show-list(fn(d') d'.show(showT))
    DefNonRec(def) -> "DefNonRec " ++ def.show(showT)

alias defs<t> = list<def<t>>;

struct valueBinder<t, e>
  name: name
  binderType: t // Always present for constructors
  expr: e // always present for definitions as 'Expr t'
                // Function and constructor parameters use 'Maybe (Expr t)' for default values.
                // Pattern bindings ('PatVar') use unit '()'.
  nameRange: range
  range: range; // full range

fun show(v: valueBinder<t,e>, showT: (t) -> e1 string, showE: (e) -> e1 string): e1 string
  v.name.show ++ " " ++ v.binderType.showT ++ " " ++ v.expr.showE ++ " " ++ v.nameRange.showFullRange ++ " " ++ v.range.showFullRange

struct def<t>
  binder: valueBinder<(), expr<t>>
  range: range
  visibilty: visibility
  sort: defSort
  defInline: defInline
  doc: string;

fun show(d: def<t>, showT: (t) -> e string): e string
  d.binder.show(fn(x) "", fn(e1) "") ++ " " ++ d.range.showFullRange ++ " " ++ d.visibilty.show ++ " " ++ d.sort.show ++ " " ++ d.defInline.show ++ " " ++ d.doc

fun defIsVal(d: def<t>): bool
  !d.sort.isFun

fun guardTrue(): expr<t>
  Var(nameTrue, False, rangeNull)

type expr<t>
  Lam(binder: list<valueBinder<maybe<t>,maybe<expr<t>>>>, e: expr<t>, range: range)
  Let(def: defGroup<t>, e: expr<t>, range: range)
  Bind(def: def<t>, e: expr<t>, range: range)
  App(e: expr<t>, args: list<(maybe<(name, range)>, expr<t>)>, range: range)
  Var(name: name, isOp: bool, range: range)
  Literal(l: lit, range: range = l.range)
  Ann(e: expr<t>, t: t, range: range)
  Case(e: expr<t>, cases: list<branch<t>>, range: range)
  Parens(e: expr<t>, name: name, range: range)
  Inject(t: t, e: expr<t>, behind: bool, range: range)
  Handler(sort: handlerSort, scope: handlerScope, hOverride: handlerOverride, allowMask: maybe<bool>, hEffect: maybe<t>, localPars: list<valueBinder<maybe<t>, ()>>, initially: maybe<expr<t>>, hReturn: maybe<expr<t>>, finally: maybe<expr<t>>, branches: list<handlerBranch<t>>, declRange: range, range: range)

fun show(expr: expr<t>, showT: (t) -> div string): div string
  match expr
    Lam(binder, e, range) -> "Lam " ++ binder.show-list(fn(b) b.show(fn(s) s.show(showT), fn(e') e'.show(fn(s) s.show(showT)))) ++ " " ++ e.show(showT) ++ " " ++ range.showFullRange
    Let(d, e, range) -> "Let " ++ d.show(showT) ++ " " ++ e.show(showT) ++ " " ++ range.showFullRange
    Bind(d, e, range) -> "Bind " ++ d.show(showT) ++ " " ++ e.show(showT) ++ " " ++ range.showFullRange
    App(e, args, range) -> "App " ++ e.show(showT) ++ " " ++ args.show-list(fn(a) "" ++ ":" ++ a.snd.show(showT)) ++ " " ++ range.showFullRange
    Var(name, isOp, range) -> "Var " ++ name.show ++ " " ++ isOp.show ++ " " ++ range.showFullRange
    Literal(l) -> "Literal " ++ l.show
    Ann(e, t, range) -> "Ann " ++ e.show(showT) ++ " " ++ t.showT ++ " " ++ range.showFullRange
    Case(e, cases, range) -> "Case " ++ e.show(showT) ++ " " ++ cases.show-list(fn(c) c.show(showT)) ++ " " ++ range.showFullRange
    Parens(e, name, range) -> "Parens " ++ e.show(showT) ++ " " ++ name.show ++ " " ++ range.showFullRange
    Inject(t, e, behind, range) -> "Inject " ++ t.showT ++ " " ++ e.show(showT) ++ " " ++ behind.show ++ " " ++ range.showFullRange
    Handler(sort, scope, hOverride, allowMask, hEffect, localPars, initially, hReturn, finally, branches, declRange, range) -> 
      "Handler " ++ sort.show ++ " " ++ scope.show ++ " " ++ hOverride.show ++ " " ++ 
      allowMask.show(show) ++ " " ++ hEffect.show(showT) ++ " " ++ localPars.show-list(fn(p) p.show(fn(f) f.show(showT), fn(s) "")) ++ " " ++ 
      initially.show(fn(e') e'.show(showT)) ++ " " ++ hReturn.show(fn(e) e.show(showT)) ++ " " ++ finally.show(fn(e) e.show(showT)) ++ " " ++
      branches.show-list(fn(b) b.show(showT)) ++ " " ++ declRange.showFullRange ++ " " ++ range.showFullRange

type handlerOverride
  HandlerOverride
  HandlerNoOverride

fun show(h: handlerOverride): string
  match h
    HandlerOverride -> "HandlerOverride"
    HandlerNoOverride -> "HandlerNoOverride"

type handlerScope
  HandlerScoped
  HandlerNoScope

fun show(h: handlerScope): string
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

fun show(h: handlerBranch<t>, showT: (t) -> div string): div string
  h.branchName.show ++ " " ++ h.branchPars.show-list(fn(p) p.show(fn(m) m.show(showT), fn(m) "")) ++ " " ++ h.branchExpr.show(showT) ++ " " ++
  h.branchSort.show ++ " " ++ h.branchNameRange.showFullRange ++ " " ++ h.branchPatRange.showFullRange
  
struct branch<t>
  branchPattern: pattern<t>
  branchGuard: guard<t>

fun show(b: branch<t>, showT: (t) -> div string): div string
  b.branchPattern.show(showT) ++ " " ++ b.branchGuard.show(showT)
  
struct guard<t>
  guardTest: expr<t>
  guardExpr: expr<t>

fun show(g: guard<t>, showT: (t) -> div string): div string
  g.guardTest.show(showT) ++ " " ++ g.guardExpr.show(showT)

type pattern<t>
  PatWild(range: range)
  PatVar(ref: valueBinder<maybe<t>, pattern<t>>, range: range= ref.range)
  PatAnn(p: pattern<t>, t: t, range: range)
  PatCon(name: name, args: list<(maybe<(name, range)>, pattern<t>)>, nameRange: range, range: range)
  PatParens(p: pattern<t>, range: range)
  PatLit(value: lit, range:range = value.range)

fun show(p: pattern<t>, showT: (t) -> div string): div string
  match p
    PatWild(range) -> "PatWild " ++ range.showFullRange
    PatVar(ref) -> "PatVar " ++ ref.show(fn(m) m.show(showT), fn(p') p'.show(showT))
    PatAnn(p, t, range) -> "PatAnn " ++ p.show(showT) ++ " " ++ t.showT ++ " " ++ range.showFullRange
    PatCon(name, args, nameRange, range) -> "PatCon " ++ name.show ++ " " ++ args.show-list(fn(a) ":" ++ a.snd.show(showT)) ++ " " ++ nameRange.showFullRange ++ " " ++ range.showFullRange
    PatParens(p, range) -> "PatParens " ++ p.show(showT) ++ " " ++ range.showFullRange
    PatLit(value) -> "PatLit " ++ value.show

type lit
  LitInt(value: int, range: range)
  LitFloat(value: float64, range: range)
  LitChar(value: string, range: range)
  LitString(value: string, range: range)

fun show(l: lit): string
  match l
    LitInt(v, r) -> v.show ++ " " ++ r.showFullRange
    LitFloat(v, r) -> v.show ++ " " ++ r.showFullRange
    LitChar(v, r) -> v ++ " " ++ r.showFullRange
    LitString(v, r) -> v ++ " " ++ r.showFullRange

// Types and kinds
alias kUserTypes<k> = list<kUserType<k>>

type userQuantifier
  QSome
  QForall
  QExists

fun show(u: userQuantifier): string
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

fun show(u: userType): div string
  match u
    TpQuan(q, b, kind, range) -> "TpQuan " ++ q.show ++ " " ++ b.show(show) ++ " " ++ kind.show ++ " " ++ range.showFullRange
    TpQual(l, kind) -> "TpQual " ++ l.show-list(fn(t) t.show) ++ " " ++ kind.show
    TpFun(a, b, c, range) -> "TpFun " ++ a.show-list(fn(t) t.fst.show ++ ":" ++ t.snd.show) ++ " " ++ b.show ++ " " ++ c.show ++ " " ++ range.showFullRange
    TpApp(a, b, range) -> "TpApp " ++ a.show ++ " " ++ b.show-list(fn(t) t.show) ++ " " ++ range.showFullRange
    TpVar(name, range) -> "TpVar " ++ name.show ++ " " ++ range.showFullRange
    TpCon(name, range) -> "TpCon " ++ name.show ++ " " ++ range.showFullRange
    TpParens(t, range) -> "TpParens " ++ t.show ++ " " ++ range.showFullRange
    TpAnn(t, kind) -> "TpAnn " ++ t.show ++ " " ++ kind.show

type userKind
  KindCon(name: name, range: range)
  KindArrow(from: userKind, to: userKind)
  KindParens(kind: userKind, range: range)
  KindNone // Flags no explicit kind annotation

fun show(u: userKind): string
  match u
    KindCon(name, range) -> "KindCon " ++ name.show ++ " " ++ range.showFullRange
    KindArrow(from, to) -> "KindArrow " ++ from.show ++ " " ++ to.show
    KindParens(kind, range) -> "KindParens " ++ kind.show ++ " " ++ range.showFullRange
    KindNone -> "KindNone"



// Range

fun range(tp: kUserType<k>, rK: (k) -> range): range
  match tp
    TpQuan(range=range) -> range
    TpQual(preds, tp) -> Range(preds.head.default(tp).unsafe-decreasing.range(rK).start, tp.range(rK).end)
    TpFun(range=range) -> range
    TpApp(range=range) -> range
    TpVar(range=range) -> range
    TpCon(range=range) -> range
    TpParens(range=range) -> range
    TpAnn(userTp, kind) -> Range(userTp.range(rK).start, kind.rK.end)

fun range(uk: userKind): range
  match uk
    KindCon(range=range) -> range
    KindArrow(k1, k2) -> Range(k1.range.start, k2.range.end)
    KindParens(range=range) -> range
    KindNone -> rangeNull

fun range(utp: userType): range
  utp.range(range)



// free type variables
fun freeTypeVars(m: maybe<a>, f: (a) -> div nameSet): div nameSet
  match m
    Nothing -> namesEmpty
    Just(x) -> f(x)

fun freeTypeVars(l: list<a>, f: (a) -> div nameSet): div nameSet
  l.foldl(namesEmpty, fn(s, x) s + f(x))

fun freeTypeVars(tp: kUserType<k>): div nameSet
  match tp
    TpQuan(_, TypeBinder(name), tp, _) -> tp.freeTypeVars - name
    TpQual(preds, tp) -> freeTypeVars(Cons(tp, preds), freeTypeVars)
    TpFun(args, eff, tp) -> freeTypeVars(Cons(tp,Cons(eff,args.map(snd))), freeTypeVars)
    TpApp(tp, args) -> tp.freeTypeVars + args.freeTypeVars(freeTypeVars)
    TpVar(name) -> namesEmpty.add(name)
    TpCon -> namesEmpty
    TpParens(tp) -> tp.freeTypeVars
    TpAnn(tp) -> tp.freeTypeVars
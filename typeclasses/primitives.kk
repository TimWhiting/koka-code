
import datastructure
import utils
// Primitives
// Type Vars
val alpha = Ident("alpha")
val alphaT = TypeVar("alpha")
val beta = Ident("beta")
val betaT = TypeVar("beta")
val zeta = Ident("zeta")
val zetaT = TypeVar("zeta")
val tAlpha = TVar(alphaT)
val tBeta = TVar(betaT)
val tZeta = TVar(zetaT)

// Primitive Expresssions
fun doFst(v: evalue): exn evalue
  match v
    Tuple(Cons(c0, _)) -> c0
    _ -> throw("Invalid argument to fst")
fun doSnd(v: evalue): exn evalue
  match v
    Tuple(Cons(_, Cons(c1, _))) -> c1
    _ -> throw("Invalid argument to snd")
fun doThd(v: evalue): exn evalue
  match v
    Tuple(Cons(_, Cons(_, Cons(c2, _)))) -> c2
    _ -> throw("Invalid argument to thd")
fun doOr(v: evalue): exn evalue
  match v
    Tuple([Bool(b0), Bool(b1)]) -> Bool(b0 || b1)
    _ -> throw("Invalid argument to or")
fun doAnd(v: evalue): exn evalue
  match v
    Tuple([Bool(b0), Bool(b1)]) -> Bool(b0 && b1)
    _ -> throw("Invalid argument to and")
fun doEqInt(v: evalue): exn evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Bool(i0 == i1)
    _ -> throw("Invalid argument to eqInt")
fun doEqChar(v: evalue): exn evalue
  match v
    Tuple([Char(c0), Char(c1)]) -> Bool(c0 == c1)
    _ -> throw("Invalid argument to eqChar")
fun doAddInt(v: evalue): exn evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Int(i0 + i1)
    _ -> throw("Invalid argument to addInt")
fun doMultInt(v: evalue): exn evalue
  match v
    Tuple([Int(i0), Int(i1)]) -> Int(i0 * i1)
    _ -> throw("Invalid argument to multInt")
fun doNegInt(v: evalue): exn evalue
  match v
    Int(i0) -> Int(0 - i0)
    _ -> throw("Invalid argument to negInt")
fun doAddFloat(v: evalue): exn evalue
  match v
    Tuple([Float(f0), Float(f1)]) -> Float(f0 + f1)
    _ -> throw("Invalid argument to addFloat")
fun doMultFloat(v: evalue): exn evalue
  match v
    Tuple([Float(f0), Float(f1)]) -> Float(f0 * f1)
    _ -> throw("Invalid argument to multFloat")
fun doNegFloat(v: evalue): exn evalue
  match v
    Float(f0) -> Float(0.0 - f0)
    _ -> throw("Invalid argument to negFloat")
  
val eFst = PrimOp(Ident("fst"), doFst, TFun([tAlpha, tBeta].tupleT, tAlpha).scheme([alphaT, betaT]))
val eSnd = PrimOp(Ident("snd"), doSnd, TFun([tAlpha, tBeta].tupleT, tBeta).scheme([alphaT, betaT]))
val eThd = PrimOp(Ident("thd"), doThd, TFun([tAlpha, tBeta, tZeta].tupleT, tZeta).scheme([alphaT, betaT, zetaT]))
val eOr = PrimOp(Ident("or"), doOr, createBinaryOpType(tBool).scheme)
val eAnd = PrimOp(Ident("and"), doAnd, createBinaryOpType(tBool).scheme)
val eEqInt = PrimOp(Ident("eqInt"), doEqInt, createEqType(tInt).scheme)
val eEqChar = PrimOp(Ident("eqChar"), doEqChar, createEqType(tChar).scheme)
val eAddInt = PrimOp(Ident("eAddInt"), doAddInt, createBinaryOpType(tInt).scheme)
val eMultInt = PrimOp(Ident("eMultInt"), doMultInt, createBinaryOpType(tInt).scheme)
val eNegInt = PrimOp(Ident("eNegInt"), doNegInt, TFun(tInt, tInt).scheme)
val eAddFloat = PrimOp(Ident("eAddFloat"), doAddFloat, createBinaryOpType(tFloat).scheme)
val eMultFloat = PrimOp(Ident("eMultFloat"), doMultFloat, createBinaryOpType(tFloat).scheme)
val eNegFloat = PrimOp(Ident("eNegFloat"), doNegFloat, TFun(tFloat, tFloat).scheme)
val primExprs = [eFst, eSnd, eThd, eOr, eAnd, eEqInt, eEqChar, eAddInt, eMultInt, eNegInt, eAddFloat, eMultFloat, eNegFloat]

fun lookupPrim(id2: ident): maybe<expr>
  with a <- primExprs.find
  match a
    PrimOp(id, _, _) | id.name == id2.name -> True
    _ -> False
import expr
import std/core/undiv

type contextexpr 
  AppFCtx(fct: expr, parent: contextexpr)
  AppACtx(arg: expr, parent: contextexpr)
  LamCtx(body: expr, vbl: string, parent: contextexpr)
  LetBCtx(body: expr, vbl: string, index: int, parent: contextexpr)
  LetExprCtx(bind: expr, vbl: string, parent: contextexpr)
  RecBCtx(body: expr, vbl: string, parent: contextexpr)
  IdCtx(parent: contextexpr)
  Op2Arg1Ctx(parent: contextexpr, arg1: expr)
  Op2Arg2Ctx(parent: contextexpr, arg2: expr)
  NumCtx(parent: contextexpr)
  If0CondCtx(parent: contextexpr, cond: expr)
  If0ThenCtx(parent: contextexpr, thn: expr)
  If0ElseCtx(parent: contextexpr, els: expr)

fun bind(v: string, c: contextexpr): contextexpr
  match c
    LamCtx(_, vbl) | vbl == v -> c.parent
    RecBCtx(_, vbl) | vbl == v -> c.parent
    LetBCtx(_, vbl, _, _) | vbl == v -> c.parent
    _ -> bind(v, c.parent.pretend-decreasing)

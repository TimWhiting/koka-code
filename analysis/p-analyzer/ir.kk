import analysis/cps/sexpr

pub alias label = int;
pub alias symbol = (int, int); // name-interned, disambiguation

val symbol_table:ref<global,list<(string, int)>> = unsafe-total{ref([])}
fun to-sexp(s: symbol): sexpr
  unsafe-total
    SName(s.fst.unintern ++ s.snd.show)

fun unintern(i: int): string
  unsafe-total
    (!symbol_table).find(fn(x) x.snd == i).default(("not interned",0)).fst

fun intern(s: string): int
  unsafe-total
    val i = (!symbol_table).find(fn(x) x.fst == s).default((s,-1)).snd
    if i != -1 then i else
      match (!symbol_table)
        [] -> 
          symbol_table.set([(s,0)])
          0
        Cons((_, x), rst) -> 
          symbol_table.set(Cons((s, x+1), rst))
          x + 1

fun sym(s: symbol)
  s.fst

fun ix(s: symbol)
  s.snd

pub struct lambda
  pub args: list<symbol>
  pub body: expr
  pub is-continuation: bool
  pub is-bind-operator: bool

pub type term
  TId(s: symbol)
  TBool(b: bool)
  TNumber(n: int)
  TLambda(l: lambda)

pub type primitiveOp
  Add
  Sub
  Mul
  Equal
  Less
  Greater
  Not
  Or
  Halt

pub type exprKind
  Call(func: term, arguments: list<term>)
  If(test: term, consequent: expr, alternative: expr)
  PrimitiveOp(op: primitiveOp, arguments: list<term>)
  Set(name: symbol, value: term, continuation: term)
  MakeStruct(tag: int, fields: list<term>, continuation: term)
  Match(value: term, match-clauses: list<(int, term)>, default-clause: maybe<term> = Nothing)

pub struct expr
  pub kind: exprKind
  pub label: label
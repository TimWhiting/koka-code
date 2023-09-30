import compiler/common/name

alias importmap = list<(list<name>, name)>

val emptyImports:importmap = []

fun isPrefix(x: list<name>, y: list<name>): bool
  match (x, y)
    (Cons(x1, xs), Cons(y1, ys)) -> x1 == y1 && isPrefix(xs.unsafe-decreasing, ys)
    (Nil, _) -> True
    _ -> False

fun importsExtend(imp: importmap, name: name, fullName: name)
  val rpath = name.splitModuleName.reverse
  match imp.lookup(fn(x) x == rpath)
    Just(fullName1) -> if fullName1 == fullName then Just(imp) else Nothing
    Nothing -> Just(Cons((rpath, fullName), imp))

// importsExpand name map@ takes a qualified name (@core/int@) and expands
// it to its real fully qualified name (@std/core/int@). It also returns
// the declared alias suffix (used to find case-errors). 
// On ambiguity, or if not found at all, it returns Left with a list of candidates.
fun importsExpand(imp: importmap, name: name): either<list<name>, (name, name)>
  if !name.isQualified then
    Right((name, nameNil))
  else 
    val rpath = name.splitModuleName.reverse
    match imp.filter(fn(x) rpath.isPrefix(x.fst))
      [(ralias, fullName)] -> 
        Right((qualify(fullName, name.unqualify), ralias.take(rpath.length).reverse.unsplitModuleName))
      amb -> Left(amb.map(fn(x) x.fst.reverse.unsplitModuleName))

fun importsList(imp: importmap): list<(name, name)>
  imp.map(fn(x) (x.fst.reverse.unsplitModuleName, x.snd))
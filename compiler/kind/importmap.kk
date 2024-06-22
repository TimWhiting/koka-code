import compiler/common/name
import std/data/linearmap
import std/core/undiv

alias importmap = linearMap<list<string>, name>

fun is-prefix(x: list<string>, y: list<string>): bool
  match (x, y)
    (Cons(x1, xs), Cons(y1, ys)) -> x1 == y1 && is-prefix(xs.pretend-decreasing, ys)
    (Nil, _) -> True
    _ -> False

fun extend(imp: importmap, name: name, fullName: name)
  val rpath = name.split-module-name.reverse
  match imp.lookup(rpath)
    Just(fullName1) -> if fullName1 == fullName then Just(imp) else Nothing
    Nothing -> Just(imp.set(rpath, fullName))

// Given a fully qualified name, return the shorter aliased name.
// import f = system/foo => system/foo/bar -> f/bar
fun get-alias(imp: importmap, nm: name)
  val mname = nm.qualifier
  match imp.entries.filter(fn((_, fullname)) mname == fullname)
    [(ralias, _)] ->
      val alias0 = ralias.reverse.unsplit-module-name
      qualify(alias0, nm.unqualify)
    _ -> nm

fun list(imp: importmap): list<(name, name)>
  imp.entries.map(fn(x) (x.fst.reverse.unsplit-module-name, x.snd))

// expand name map@ takes a qualified name (@core/int@) and expands
// it to its real fully qualified name (@std/core/int@). It also returns
// the declared alias suffix (used to find case-errors). 
// On ambiguity, or if not found at all, it returns Left with a list of candidates.
fun expand(imp: importmap, name: name): exn either<list<name>, (name, name)>
  val rpath = name.qualifier.split-module-name.reverse
  imp.resolve-path(name.unqualify, rpath)

fun resolve-path(imp: importmap, basename: name, rpath: list<string>): exn either<list<name>, (name, name)>
  if rpath.length == 0 then return Right((basename, nil))
  match imp.entries.filter(fn((ralias, _)) -> rpath.is-prefix(ralias))
    [] -> // No match - assume local qualification (note: rpath cannot be null)
      match rpath
        Cons(q, qs) -> 
          match imp.resolve-path(basename, qs)
            Right((qname, aliased)) -> Right((q.new-module-name.qualify-locally(qname), aliased))
            Left(err) -> Left(err)
    [(ralias, modName)] -> // Unique match
      val qname = qualify(modName, basename)
      val aliased = ralias.take(rpath.length).unsplit-module-name
      Right((qname, aliased))
    amb -> Left(amb.map(fn(x) x.fst.reverse.unsplit-module-name))


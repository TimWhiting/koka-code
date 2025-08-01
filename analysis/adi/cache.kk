import ev
import abev
import expr
import utils
import std/data/linearmap
import std/data/linearset

alias cache-entry<a,s> = linearSet<(s, linearMap<a, s>)>
alias cache<a,s,p> = linearMap<(expr, p, linearMap<a, s>), cache-entry<a, s>>
alias abkey = (expr, env<int>, linearMap<int, abvalue<int>>)
alias abentry = cache-entry<int, abvalue<int>>
alias abcache = cache<int, abvalue<int>, env<int>>
effect ecache<a, s, p>
  fun get-cache-out(): cache<a,s,p>
  fun get-cache-in(): cache<a,s,p>
  fun put-cache-out(c: (expr, p, linearMap<a,s>), s: cache-entry<a,s>): ()
  fun update-cache(c: (expr, p, linearMap<a, s>), v: s, s: linearMap<a,s>): ()
  val eq-v-store: (some<e> ((s, linearMap<a,s>), (s, linearMap<a,s>)) -> e bool)

effect ecachevisit<a, s>
  ctl visit-cache(s: cache-entry<a,s>): (s, linearMap<a,s>)

alias cacheval = (abvalue<int>, linearMap<int,abvalue<int>>)

val emptyCacheValStore = LinearSet([(Abvalue(Nothing, Nothing), LinearMap([]))])
alias arinterp<a,s> = <rinterp<a,s>,ecache<a,s,env<a>>,ecachevisit<a,s>>
alias rarinterp<e> = (expr) -> <arinterp<int, abvalue<int>>|e> abvalue<int>

fun evcache(ev0 : (rarinterp<e> -> rarinterp<e>)): <> (rarinterp<e> -> rarinterp<e>)
  fn(ev: some<e> rarinterp<e>)
    fn(e: expr)
      val p = ask-env()
      val s = get-store()
      val config = (e, p, s)
      val out = get-cache-out()
      if out.contains-key(config) then
        val v-store = out.lookup(config)
        match v-store
          Just(v-store') | !v-store'.is-empty ->
            val (v, store) = visit-cache(v-store')
            put-store(store)
            v
          _ -> fail()
      else
        val inC = get-cache-in()
        val v-store = inC.get-default(config, LinearSet([]))
        put-cache-out(config, v-store)
        val v = ev0(ev)(e)
        val s' = get-store()
        update-cache(config, v, s')
        v

val emptyCache = LinearMap([])

fun fixcache(eval: rarinterp<e>, e: expr): <div,exn|e> abvalue<int>
  var cachein := emptyCache
  var cacheout := emptyCache
  with handler
    val eq-v-store = fn(a: cacheval, b: cacheval) a == b
    fun get-cache-in() cachein
    fun get-cache-out() cacheout
    fun put-cache-out(c: abkey, s: abentry)
      cacheout := cacheout.set(c, s)
    fun update-cache(c: abkey, v: abvalue<int>, s: linearMap<int, abvalue<int>>)
      cacheout := cacheout.update(c, emptyCacheValStore.add((v, s)), fn(o, n) n.add((v, s)))
  with default-env
  with handle-store
  with handleAbsValue
  with handler 
    final ctl fail() injC(ErrorV)
  with handleAbsNdet
  val p = ask-env()
  val s = get-store()
  val config = (e, p, s)
  // var iter := 0
  val newCache = mlfp() fn(cache)
    cacheout := emptyCache
    put-store(s)
    cachein := cache
    // trace("Cache Iter " ++ iter.show)
    val x = mask<local>{evalvisit(eval, e)}
    // trace("Cache Iter Finished " ++ iter.show)
    // iter := iter + 1
    get-cache-out()
  val vstore = newCache.get(config)
  // trace("Getting final result")
  val (v, store) = vstore.list.foldl((injC(ErrorV), emptyAbsStore)) fn(acc: (abvalue<int>, linearMap<int, abvalue<int>>), c2: cacheval)
      val (v, s1) = c2
      val (vacc, sacc) = acc
      (vacc.join(v), sacc.join(s1))
  put-store(store)
  v

fun evalvisit(eval: rarinterp<e>, e:expr): <rinterp<int, abvalue<int>>,ecache<int, abvalue<int>, env<int>>|e> abvalue<int>
  with handler
    ctl visit-cache(c) c.list.foldl(injC(ErrorV)) fn(acc: abvalue<int>, c2: cacheval)
      val (v, s1) = c2
      acc.join(resume((v, s1)))
  eval(e)

// fun showCacheDiff(c: abcache, c1: abcache): <div|e> string
//   val literallyNew = c1.list.filter(fn(e) !c.containsKey(e.fst))
//   val changed = c1.list.filter fn(e)
//     match c.lookup(e.fst)
//       Just(v) -> !(c1.eqV)(e.snd, v)
//       _ -> False
//   "\nNew configs\n" ++
//   literallyNew.showNewlineList(fn((k, v)) (c.showK)(k) ++ "\n\t=> " ++ (c.showV)(v)) ++
//   "\nChanged configs\n" ++
//   changed.showNewlineList(fn((k, v)) (c.showK)(k) ++ "\n\twas:" ++ c.maybeGet(k).map(fn(e) (c.showV)(e)).default("Nothing") ++ "\n\t=> " ++ (c.showV)(v))
  
// fun showNewlineList(l: list<a>, showA: (a) -> e string): e string
//   if l.is-nil then
//     "Empty List"
//   else
//     l.foldl("") fn(acc, a) acc ++ "\n" ++ showA(a)

fun mlfp(f: (abcache) -> <div|e> abcache, x:abcache = emptyCache): <div|e> abcache
  val x' = f(x)
  if x' == x then 
    // "Should be done iterating".trace
    x
  else
    // "Cache Diff".trace
    // x.showCacheDiff(x').trace 
    mlfp(f, x')

// fun docacheev(e)
//   fix(evcache(evabs(ev')))(e)

// fun docachetell(e)
//   fix(evtell2(evcache(evabs(ev'))))(e)

// fun evtell2(ev0)
//   fn(ev)
//     fn(e)
//       with override
//         fun tell(e', d)
//           tell(e', d)
//         fun tellResult(e', d)
//           tellResult(e', d)
//         val expressionDepth = expressionDepth + 1
//       tell((e, ask-env(), get-store()), expressionDepth)
//       tellResult(ev0(ev)(e), expressionDepth)
      
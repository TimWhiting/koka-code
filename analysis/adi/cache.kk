import ev
import abev
import expr
import utils
import newstd/data/linearmap
import newstd/data/linearset

alias cache-entry<a,s> = linearSet<(s, linearMap<a, s>)>
alias cache<a,s,p> = linearMap<(expr, p, linearMap<a, s>), cache-entry<a, s>>

alias abcache = cache<int, abvalue<int>, env<int>>
alias cachinterp = <exn,div,fail<abvalue<int>>,primop<int,abvalue<int>,env<int>>,eenv<int,env<int>>,estore<int,abvalue<int>,env<int>>,ecache<int, abvalue<int>, env<int>>>
effect ecache<a, s, p>
  fun get-cache-out(): cache<a,s,p>
  fun get-cache-in(): cache<a,s,p>
  fun put-cache-out(c: (expr, p, linearMap<a,s>), s: cache-entry<a,s>): ()
  ctl visit-cache(s: cache-entry<a,s>): (s, linearMap<a,s>)
  fun update-cache(c: (expr, p, linearMap<a, s>), v: s, s: linearMap<a,s>): ()
  val eq-v-store: (some<e> ((s, linearMap<a,s>), (s, linearMap<a,s>)) -> e bool)

alias cacheval = (abvalue<int>, linearMap<int,abvalue<int>>)
fun eqCacheValue(s1: cacheval, s2: cacheval): div bool
  (==)(s1.fst, s2.fst, (==), fn(s) s.show) && s1.snd == s2.snd

fun show(c: config)
  val (e, p, s) = c
  expr/show(e) ++ " " ++ utils/show(p, core/show) ++ " " ++ linearmap/show(s)

val emptyCacheValStore = linearSet([(Abvalue(Nothing, Nothing), linearMap([], fn(i1, i2: int) i1 == i2, fn(a1: abvalue<int>, a2: abvalue<int>) (==)(a1, a2, (==), showA), fn(k) k.show, fn(v) v.show(showA)))], eqCacheValue, fn(s) s.fst.show(showA) ++ "," ++ s.snd.show)
alias arinterp<a,s> = <rinterp<a,s>,ecache<a,s,env<a>>>
alias rarinterp<e> = (expr) -> <arinterp<int, abvalue<int>>|e> abvalue<int>
alias rrinterp<e> = (expr) -> <rinterp<int, abvalue<int>>|e> abvalue<int>

fun evcache(ev0 : (rarinterp<e> -> rarinterp<e>)): <> (rarinterp<e> -> rarinterp<e>)
  fn(ev)
    fn(e)
      val p = ask-env()
      val s = get-store()
      val config = (e, p, s)
      val out = get-cache-out()
      if out.containsKey(config) then
        val v-store = out.maybeGet(config)
        match v-store
          Just(v-store') | !v-store'.is-empty ->
            val (v, store) = visit-cache(v-store')
            put-store(store)
            v
          _ -> fail()
      else
        val inC = get-cache-in()
        val v-store = inC.getDefault(config, linearSet([], eq-v-store, fn(s':(abvalue<int>, linearMap<int, abvalue<int>>)) s'.fst.show(showA) ++ "," ++ s'.snd.show))
        put-cache-out(config, v-store)
        val v = ev0(ev)(e)
        val s' = get-store()
        update-cache(config, v, s')
        v

val emptyCache = linearMap([], eqConfig, fn(a:cache-entry<int,abvalue<int>>, b:cache-entry<int,abvalue<int>>) a == b, show, show)

fun fixcache(eval: rarinterp<e>, e: expr): <div,exn|e> abvalue<int>
  var cachein := emptyCache
  var cacheout := emptyCache
  with handler 
    final ctl fail() injC(ErrorV)
  with handleAbsValue
  with default-env
  with handle-store
  with handler
    val eq-v-store = fn(a: (abvalue<int>, linearMap<int,abvalue<int>>), b: (abvalue<int>, linearMap<int,abvalue<int>>)) eqAbsV(a.fst, b.fst) && a.snd == b.snd
    fun get-cache-in() cachein
    fun get-cache-out() cacheout
    fun put-cache-out(c, s)
      cacheout := cacheout.set(c, s)
    ctl visit-cache(c) c.list.foldl(injC(ErrorV)) fn(acc: abvalue<int>, c2: cacheval)
      val (v, s) = c2
      acc.join(resume((v, s)))
    fun update-cache(c, v, s)
      cacheout := cacheout.update(c, emptyCacheValStore.add((v, s)), fn(o, n) o.add((v, s)))
  val p = ask-env()
  val s = get-store()
  val config = (e, p, s)
  val newCache = mlfp() fn(cache)
    cacheout := emptyCache
    put-store(s)
    cachein := cache
    val x = mask<local>{eval(e)}
    get-cache-out()
  val vstore = newCache.get(config)
  val (v, store) = visit-cache(vstore)
  put-store(store)
  v

fun mlfp(f: (abcache) -> <div|e> abcache, x:abcache = emptyCache): <div|e> abcache
  val x' = f(x)
  // "Run 1".trace
  // x.show.trace
  // "After".trace
  // x'.show.trace
  // "".trace
  val eq = x' == x
  val eq2 = x.show == x'.show
  // ("eq: " ++ eq.show).trace
  if (eq != eq2) then
    x.show.trace
    "After".trace
    x'.show.trace
  if eq then x
  else mlfp(f, x')

fun docacheev(e)
  fix(evcache(ev'))(e)

fun docachetell(e)
  fix(evcache(evtell(ev')))(e)
import ev
import abev
import expr
import utils
import newstd/data/linearmap
import newstd/data/linearset

alias cache-entry<a,s> = linearSet<(s, linearMap<a, s>)>
alias cache<a,s,p> = linearMap<(expr, p, linearMap<a, s>), cache-entry<a, s>>

alias abcache = cache<int, abvalue<int>, env<int>>
effect ecache<a, s, p>
  fun get-cache-out(): cache<a,s,p>
  fun set-cache-out(c: cache<a,s,p>): ()
  fun get-cache-in(): cache<a,s,p>
  fun set-cache-in(c: cache<a,s,p>): ()
  fun put-cache-out(c: (expr, p, linearMap<a,s>), s: cache-entry<a,s>): ()
  ctl visit-cache(s: cache-entry<a,s>): (s, linearMap<a,s>)
  fun update-cache(c: (expr, p, linearMap<a, s>), v: s, s: linearMap<a,s>): ()
  val eq-v-store: (some<e> ((s, linearMap<a,s>), (s, linearMap<a,s>)) -> e bool)

alias cacheval = (abvalue<int>, linearMap<int,abvalue<int>>)
fun eqCacheValue(s1: cacheval, s2: cacheval): div bool
  (==)(s1.fst, s2.fst, (==)) && eqStore(s1.snd, s2.snd)

fun eqCache(c1: cache<int, abvalue<int>, env<int>>, c2: cache<int, abvalue<int>, env<int>>)
  (==)(c1, c2, fn(s1, s2) (==)(s1, s2))

val emptyCacheValStore = linearSet([(Abvalue(Nothing, Nothing), linearMap([], fn(i1, i2: int) i1 == i2))], eqCacheValue)

fun evcache(ev0)
  fn(ev)
    fn(e)
      val p = ask-env()
      val s = get-store()
      val config = (e, p, s)
      val out = get-cache-out()
      if out.containsKey(config) then
        val v-store = out.get(config)
        val (v, store) = visit-cache(v-store)
        put-store(store)
        ret(v)
      else
        val inC = get-cache-in()
        val v-store = inC.getDefault(config, linearSet([], eq-v-store))
        put-cache-out(config, v-store)
        val v = ev0(ev)(e)
        val s' = get-store()
        update-cache(config, v, s')
        ret(v)

// fun fixcache(eval)
//   with handler
//     fun get-cache-out() get-cache-out()
//     fun set-cache-out(c) set-cache-out(c)
//     fun get-cache-in() get-cache-in()
//     fun set-cache-in(s) set-cache-in(s)
//     ctl visit-cache(c) resume(visit-cache(c))
//     fun put-cache-out(c,s) put-cache-out(c,s)
//     fun update-cache(c, v, s) update-cache(c, v, s)
//     val eq-v-store = eq-v-store
//   fn(e)
//     val p = ask-env()
//     val s = get-store()
//     val config = (e, p, s)
//     val newCache = mlfp() fn(cache)
//       set-cache-out(linearMap([], eqConfig))
//       put-store(s)
//       set-cache-in(cache)
//       val res = eval(e)
//       get-cache-out()
//     val vstore = newCache.get(config)
//     val (v, store) = visit-cache(vstore)
//     put-store(store)
//     ret(v)

// fun mlfp(f: (abcache) -> <rinterp<int, abcache>|e> abcache)
//   fun loop(x:abcache = linearMap([], eqConfig)): <rinterp<int, abcache>|e> abcache
//     val x' = f(x)
//     if eqCache(x', x) then x
//     else loop(x')
//   loop
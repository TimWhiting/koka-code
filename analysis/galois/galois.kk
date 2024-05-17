import data
import std/data/linearset
import std/data/linearmap

fun lset(eq: (a, a) -> e bool): lattice<linearSet<a>,e>
  Lattice([], fn(l, a) setunion(l, a, eq), list-eq(eq))

fun lmap(l: lattice<list<b>,e>, eqK: (a, a) -> e bool): lattice<list<(a,list<b>)>,e>
  val (bottom, union, eq) = l
  val nunion = fn(h0, h1) h1.foldl(h0, fn(acc, (k, v)) acc.update(k, fn(b1) union(b1, v), bottom, eqK))
  Lattice([], nunion, list-eq(tup-eq(eqK, eq)))

fun lpowerset(a: lattice<a,e>, b: lattice<b,e>): lattice<(a, b),e>
  val bottom = (a.bottom, b.bottom)
  val union = fn((a1, b1), (a2, b2)) (a.union()(a1, a2), b.union()(b1, b2))
  val eq = tup-eq(a.eq, b.eq)
  Lattice(bottom, union, eq)

fun cache(bottom: s, union: (s, s) -> e s, singleton: (c, r) -> e s, lookup: (s, c) -> e r, eq: (c, c) -> e bool): e1 (((c) -> e ((list<c>, s) -> e (r, s))) -> ((c) -> e ((list<c>, s) -> e (r, s))))
  fn(exec)
    fn(config)
      fn(seen, s)
        val (x, sig) = if setmember(seen, config, eq) then (lookup(s, config), bottom) else exec(config)(setadd(seen, config, eq), s)
        (x, union(sig, singleton(config, x))) 

fun lfp((bottom, _, _): lattice<a,e>, f: (a) -> e a, eq: (a, a) -> e bool): e a
  fun loop(x0)
    val x = f(x0)
    if (eq(x,x0)) then x else loop(x0.unsafe-decreasing)
  loop(bottom)

fun fix(f: (a) -> e a): e a
  f(fix(f.unsafe-decreasing))

fun makeeval(monad)
  val Monad(unit, bind, sigma-lookup, sigma-extend) = monad
  fn(eval)
    fn(expr: expr, rho: list<(string, string)>)
      match expr
        Symbol(x) -> 
          val v = try{rho.getKey(x, eq-string)}.default("-not-present")
          if v == "-not-present" then
            unit(CompileError("Not present in environment"))
          else 
            sigma-lookup(v)
        Lam(_, _) -> unit(Clos(expr, rho))
        App(e1, e2) -> 
          with f <- bind(eval(e1, rho))
          match f
            Clos(Lam(x, e), p) -> 
              with v <- bind(eval(e2, rho))
              val alpha = x
              val rho' = p.setVal(x, alpha, eq-string)
              with _ <- bind(sigma-extend(alpha, v))
              eval(e, rho')
            _ -> unit(CompileError("function not a closure"))

fun run(l, m, inj, singleton, lookup, alpha, gamma, strip,
        make-ev-expr,
        eq-c, pr)
  // val Analysis() = analysis 
  val (bottom, union, eq) = l
  val sigma = inj(pr)
  val eval-cach = fn(eval) alpha(cache(bottom, union, singleton, lookup, eq-c)(gamma(eval)))
  val eval-expr = make-ev-expr(m)
  val eval = fix(fn(ev) (eval-cach(eval-expr(ev))))
  lfp(l, strip(gamma(eval))(sigma), eq)

// fun mps-monad()
  

// val ppsanalysis = 

alias aconfig = (expr,trho,absstore)
alias configstore = list<((evalue, trho), absstore)>
alias abvaluestore = list<(evalue, absstore)>
alias mps = some<e> absstore -> ((abvaluestore, configstore) -> e (abvaluestore, list<(aconfig, list<abvaluestore>)>))
val aconfigeq = tup3-eq(eq-value,eq-rho,absstore-eq)

fun runpps(expr: expr)
  val unit = fn(v) fn(sig) fn(seen, sigma) ([(v, sig)], [])
  val (bvs, uvs, _) = lset(tup-eq(eq-value, absstore-eq))
  val othereq = tup-eq(eq-value, absstore-eq)
  val (bcch, ucch, _) = lmap(lset(list-eq(othereq)),aconfigeq)
  val bind = fn(c,f)
    fn(sig: absstore)
      fn(seen:abvaluestore, cch: configstore)
        val (vs_sig0, cch0) = c(sig)(seen, cch)
        val (vs_sign, cchn) = vs_sig0.foldl((bvs, bcch)) fn(acc, (v,s))
          val (vs_sig1, cch1) = acc
          val (vs_sig2, cch2) = f(v)(s)(seen, cch)
          (uvs(vs_sig1, vs_sig2), ucch(cch1, cch2))
        (vs_sign, ucch(cch0, cchn))
  val sig-lookup = fn(a)
    fn(sig: absstore)
      fn(seen, cch)
        val vs = sig.getKeyDefault(a, eq-string, []).map(fn(v) (v, sig))
        (vs, [])
  val sig-extend = fn(a, v)
    fn(sig: absstore)
      fn(seen, cch)
        val newv = [(Dummy, sig.update(a, fn(vs) setadd(vs, v, eq-value), [], eq-string))]
        (newv, [])
  
  run(
      lmap(lset(eq-value), aconfigeq),
      Monad(unit, bind, sig-lookup, sig-extend),
      fn(v) (v, [], []),
      fn(c, vs_sigs) [(c, vs_sigs)],
      fn(cch, c) try{cch.getKey(c, aconfigeq)}.default([]),
      fn(exec) fn(e, rho) fn(sig) exec((e, rho, sig)),
      fn(eval) fn((e, p, sig)) eval(e, p)(sig),
      fn(exec) fn(c) fn(cch)
        val (_,cchr) = exec(c)([], cch)
        cchr
    , makeeval, aconfigeq, expr)

// fun main()
//   runpps(App(Lam("x", Symbol("x")), Lam("y", Symbol("y"))))


// fun mfi-monad(): monad<evalue, mfi, string>
//   val unit = fn(v) fn(seen, sigma, cch) ([v], [], [])
//   val (bvs, uvs, _) = lset(eq-value)
//   val (bcch, ucch, _) = lmap(lset(eq-value),eq-string)
//   val (bsig, usig, _) = lmap(lset(eq-value),eq-string)
//   val bind = fn(c: mfi, f: (evalue) -> mfi): mfi
//     fn(seen, sig, cch)
//       val (vs0, sig0, cch0) = c(seen, sig, cch)
//       val (vsn, sign, cchn) = vs0.foldl((bvs, bsig, bcch)) fn(acc, v)
//         val (vs1, sig1, cch1) = acc;
//         val (vs2, sig2, cch2) = f(v)(seen, sig, cch)
//         (uvs(vs1, vs2), usig(sig1, sig2), ucch(cch1, cch2))
//       (vsn, usig(sig0, sign), ucch(cch0, cchn))
//   val sig-lookup = fn(a)
//     fn(seen, sig, cch)
//       val v = try{sig.getKey(a, eq-string)}.default([])
//       (v, [], [])
//   val sig-extend = fn(a, v)
//     fn(seen, sig, cch)
//       val sig' = sig.setVal(a, [v], eq-string)
//       ([], sig', [])
//   Monad(unit, bind, sig-lookup, sig-extend)

// fun runpfi(e: expr)
//   run(
//     lpowerset(lmap(lset(eq-value),eq-string), lmap(lset(eq-value),eq-string)),
//     mfi-monad(),
//     fn(pr: expr) (pr, []), // inj
//     fn(c: config, vs_sigs) ([], [(c, vs_sigs)]), // singleton
//     fn((sig, cch), c:config) try{cch.getKey(c, config-eq)}.default([]), // lookup
//     fn(exec) 
//       fn(e: expr, rho: trho) 
//         fn(seen: list<config>, sig, cch)
//           val (vs, (sign, cchn)) = exec((e, rho))(seen, (sig, cch))
//           (vs, sign, cchn) // alpha
//     ,
//     fn(eval)
//       fn((e:expr, p:trho))
//         fn(seen: list<config>, (sig, cch))
//           val (vs, nsig, ncch) = eval(e, p)(seen, sig, cch)
//           (vs, nsig, ncch) // gamma
//     ,
//     fn(exec)
//       fn(c:config)
//         fn(sigcch)
//           val (vs, nsigcch) = exec(sig)([], sigcch)
//           nsigcch // strip
//     ,
//     make-eval-expr,
//     App(Lam("x", Symbol("x")), Lam("y", Symbol("y"))))

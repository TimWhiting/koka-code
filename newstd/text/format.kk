infixl 80 (+)

effect formatter<t>
  fun fvalue(): t

alias format1<a> = some<e> (() -> <formatter<a>|e> string)
alias format2<a,b> = some<e>  (() -> <formatter<a>, formatter<b>|e> string)
alias format3<a,b,c> = some<e> (() -> <formatter<a>, formatter<b>, formatter<c>|e> string)
alias format4<a,b,c,d> = some<e> (() -> <formatter<a>, formatter<b>, formatter<c>, formatter<d>|e> string)
alias format5<a,b,c,d,e> = some<e1> (() -> <formatter<a>, formatter<b>, formatter<c>, formatter<d>, formatter<e>|e1> string)
alias format6<a,b,c,d,e,f> = some<e1> (() -> <formatter<a>, formatter<b>, formatter<c>, formatter<d>, formatter<e>, formatter<f>|e1> string)
alias format7<a,b,c,d,e,f,g> = some<e1> (() -> <formatter<a>, formatter<b>, formatter<c>, formatter<d>, formatter<e>, formatter<f>, formatter<g>|e1> string)
alias format8<a,b,c,d,e,f,g,h> = some<e1> (() -> <formatter<a>, formatter<b>, formatter<c>, formatter<d>, formatter<e>, formatter<f>, formatter<g>, formatter<h>|e1> string)
alias format9<a,b,c,d,e,f,g,h,i> = some<e1> (() -> <formatter<a>, formatter<b>, formatter<c>, formatter<d>, formatter<e>, formatter<f>, formatter<g>, formatter<h>, formatter<i>|e1> string)
alias format10<a,b,c,d,e,f,g,h,i,j> = some<e1> (() -> <formatter<a>, formatter<b>, formatter<c>, formatter<d>, formatter<e>, formatter<f>, formatter<g>, formatter<h>, formatter<i>, formatter<j>|e1> string)

fun fint(): format1<int>
  fn()
    val x: int = fvalue()
    x.show

fun fbool(): format1<bool>
  fn()
    if fvalue() then "true" else "false"

fun ffloat(precision: int): format1<float64>
  fn()
    val x:float64 = fvalue()
    x.show(precision)

fun (+)(f: () -> e string, s: string): (() -> e string)
  fn()
    f() ++ s

fun (+)(a: () -> e string, b: () -> <formatter<b>|e> string): (() -> <formatter<b>|e> string)
  fn()
    val ar:string = mask<formatter>{a()}
    val br:string = b()
    ar ++ br

fun (+)(s: string, f: () -> e string): (() -> e string)
  fn()
    s ++ f()

fun format(f: format1<t>, t: t): e string
  with handler fun fvalue() t
  f()

fun format(f: format2<a, b>, b: b, a: a): e string
  with handler fun fvalue() b
  with handler fun fvalue() a
  f()

fun format(f: format3<a, b, c>, c: c, b: b, a: a): e string
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f()

fun format(f: format4<a, b, c, d>, d: d, c: c, b: b, a: a): e string
  with handler fun fvalue() d
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f()

fun format(f: format5<a, b, c, d, e>, e: e, d: d, c: c, b: b, a: a): e1 string
  with handler fun fvalue() e
  with handler fun fvalue() d
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f()

fun format(f1: format6<a, b, c, d, e, f>, f: f, e: e, d: d, c: c, b: b, a: a): e1 string
  with handler fun fvalue() f
  with handler fun fvalue() e
  with handler fun fvalue() d
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f1()

fun format(f1: format7<a, b, c, d, e, f, g>, g: g, f: f, e: e, d: d, c: c, b: b, a: a): e1 string
  with handler fun fvalue() g
  with handler fun fvalue() f
  with handler fun fvalue() e
  with handler fun fvalue() d
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f1()

fun format(f1: format8<a, b, c, d, e, f, g, h>, h: h, g: g, f: f, e: e, d: d, c: c, b: b, a: a): e1 string
  with handler fun fvalue() h
  with handler fun fvalue() g
  with handler fun fvalue() f
  with handler fun fvalue() e
  with handler fun fvalue() d
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f1()

fun format(f1: format9<a, b, c, d, e, f, g, h, i>, i: i, h: h, g: g, f: f, e: e, d: d, c: c, b: b, a: a): e1 string
  with handler fun fvalue() i
  with handler fun fvalue() h
  with handler fun fvalue() g
  with handler fun fvalue() f
  with handler fun fvalue() e
  with handler fun fvalue() d
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f1()

fun format(f1: format10<a, b, c, d, e, f, g, h, i, j>, j: j, i: i, h: h, g: g, f: f, e: e, d: d, c: c, b: b, a: a): e1 string
  with handler fun fvalue() j
  with handler fun fvalue() i
  with handler fun fvalue() h
  with handler fun fvalue() g
  with handler fun fvalue() f
  with handler fun fvalue() e
  with handler fun fvalue() d
  with handler fun fvalue() c
  with handler fun fvalue() b
  with handler fun fvalue() a
  f1()

// fun main()
//   val f1 = fint() + " " + ffloat(3) + " " + fbool() + " " + fbool()
//   val s = f1.format(0, 0.21023123, True, False)
//   s.println

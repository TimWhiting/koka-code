pub effect step-ctl<a,b>
  ctl fail(a: a): ()
  ctl pause(b: b): ()

fun step-ctl-fmap<a,b,c,x,y,e>(
    fax: (a)->x,
    fby: (b)->y,
    th: () -> <step-ctl<a,b>,step-ctl<x,y>|e> c
  ): <step-ctl<x,y>|e> c
  with handler
    ctl fail(a)
      fail(a.fax)
      resume(()) // never happens
    ctl pause(b)
      pause(b.fby)
      resume(())
  th()
fun this-works( action : () -> e (a, b) ) : e a
  action().fst

fun this-also-works( action : () -> e (a, b) ) : e a
  fun extract( x : (a, b) ) : a
    x.fst
  action().extract

fun this-wont-work( action : () -> e (a, b) ) : e a
  with return( x: some<a,b> (a,b) ) x.fst
  action()
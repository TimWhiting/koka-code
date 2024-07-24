effect eff1
  fun eff1(): ()
effect eff2
  fun eff2(): ()

fun higher-order1(f: (int) -> <eff1> int, x: int): <eff1, eff2> int 
  f(x)

fun higher-order2(f: (int) -> <eff1|e> int, x: int): <eff1, eff2|e> int
   mask<eff2>
    f(x)
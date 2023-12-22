scoped effect heap<s::S> 
  control new-ref(init:a) : ref<s,a>

named effect ref<s::S,a::V> in heap<s>
  fun get() : a
  fun set(value : a) : ()

fun with-ref(init,action) 
  var s := init
  with handler
    finally {}
    return(x) x
  // BUT THIS WORKS!
  // with finally {}
  with r = named handler 
    fun get() { s  }
    fun set(x){ s := x }  
  action(r)

fun heap(action : forall<s::S> () -> <heap<s>,div|e> a) : <div|e> a
  with control new-ref(init)
    with-ref(init,resume)
  action()

fun dynamic-ref(init)
  val x = new-ref(init)
  x

public fun main()
  with heap
  with r0 = with-ref(40)
  val r1 = new-ref(41)
  val r2 = dynamic-ref(True)
  println( r0.get() + r1.get() + (if r2.get() then 1 else 0) ) 
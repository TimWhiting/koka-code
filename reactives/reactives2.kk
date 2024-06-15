named rec effect rref<s::S, a::V> in providerHeap<s>
  fun emit(a: a): ()
  ctl watch_<b>(p: provider<s,b>, immediate: bool): b
  ctl yield(): ()

scoped rec effect providerHeap<s::S>
  ctl mkProvider<a,e>(reactor: ev<rref<s,a>> -> <pure,providerHeap<s>,st<global>|e> a, name: string, show: (a) -> <pure,providerHeap<s>,st<global>|e> string): provider<s,a>

fun watch(r: ev<rref<s,a>>, p: provider<s,b>, immediate: bool = True): <pure,providerHeap<s>,st<global>> b
  r.watch_(p, immediate)

rec type provider<s,a>
  Provider(
    listeners: some<e> ref<global, list<(a) -> <pure,providerHeap<s>,st<global>|e> ()>>,
    current: some<e> () -> <pure,providerHeap<s>,st<global>|e> a,
    r: ref<global, maybe<ev<rref<s,a>>>>,
    name: string
  )

fun heap(action: forall<s> () -> <providerHeap<s>,pure|e> ()): <pure|e> ()
  with handler
    ctl mkProvider(reactor: some<s> forall<a,e> ev<rref<s,a>> -> <pure,providerHeap<s>,st<global>|e> a, name: string, show: some<s> forall<e,a> (a) -> <pure,providerHeap<s>,st<global>|e> string)
      val lcurrent : some<a> ref<global, maybe<a>> = ref(Nothing)
      val r : some<a> ref<global, maybe<ev<rref<s,a>>>> =  ref(Nothing)
      val listeners0 : some<a,e> ref<global, list<(a) -> <pure,providerHeap<s>,st<global>|e> ()>> = ref(Nil)
      val continuex: ref<global, () -> e ()> = ref(fn(){})
      val doInit = fn(r1)
          trace("doInit")
          r1.yield()
          trace("doneYield")
          val x = reactor(r1)
          r1.emit(x)
          x
      with x <- named handler
        fun emit(a)
          lcurrent := Just(a)
          ("emitting " ++ showA(a)).trace
          (!listeners0).foreach fn(l)
            l(a)
        raw ctl yield()
          ("yielding from " ++ providerName).trace
          continuex := (fn() {rcontext.resume(())})
        raw ctl watch_(o:some<s,b> provider<s,b>, triggerImmediately)
          (providerName ++ " watching " ++ o.name).trace
          o.listeners.set(Cons(fn(b) {rcontext.resume(b)}, !(o.listeners)))
          if triggerImmediately then
            (o.current)()
            ()
      r.set(Just(x))
      val provider = Provider(listeners0, fn(){ 
        match !lcurrent
          Nothing -> 
            match !r
              Just(r') -> 
                "initializing".trace
                val x' = doInit(r')
                x'.showA.trace 
                x'
              Nothing -> throw("Provider " ++ providerName ++ " not initialized")
          Just -> 
            "continuing".trace
            (!continuex)()
            match !lcurrent
              Just(k') -> k'
        },
        r,providerName)
      resume(provider)
  action()  
 

fun main()
  val result = try
    with heap
    val oProvider = mkProvider(
      fn(r: ev<rref<s,int>>) {
        r.emit(1)
        r.emit(2)
        0
      },
      fn (x: int) x.show,
      "o"
    )
    val sProvider = mkProvider(
      fn(r: ev<rref<s,int>>){
        trace("Hi")
        r.emit(100)
        val x = r.watch(oProvider, True)
        trace("X: " ++ x.show)
        1
      },
      fn(x:int) x.show,
      "s"
    );
    (sProvider.current)().show.trace
  match result
    Ok(x) -> x.show
    Error(e) -> e.show
named effect rref<a>
  fun emit(a: a): ()
  ctl watch_<b>(p: provider<b>, immediate: bool): b
  ctl yield(): ()

fun watch(r: rref<a>, p: provider<b>, immediate: bool = True): io b
  r.watch_(p, immediate)

type container
  Container(
    providers: ref<global, list<forall<a> provider<a>>>
    // TODO: Provider state
    // TODO: Store provider resumptions
    // TODO: Store provider subscriptions to other provider states
    // 
  )

rec type provider<a>
  Provider(
    listeners: ref<global, list<(a) -> io ()>>,
    current: () -> io a,
    r: ref<global, maybe<rref<a>>>
  )

fun initProvider(r:rref<a>, reactor: rref<a> -> io a, current: ref<global, maybe<a>>): io ()
  val x = reactor(r)
  current := Just(x)

fun mkProvider(reactor: rref<a> -> io a, show: (a) -> io string, name="Provider"): io provider<a>
  val lcurrent : some<a> ref<global, maybe<a>> = ref(Nothing)
  val r : some<a> ref<global, maybe<rref<a>>> =  ref(Nothing)
  val continuex: ref<global, () -> io ()> = ref(fn(){})
  val doInit = fn(r1)
      r1.yield()
      val x = reactor(r1)
      r1.emit(x)
  val pr = Provider(ref([]), fn(){ 
    match !lcurrent
      Nothing -> 
        (!continuex)()
        match !lcurrent
          Nothing -> throw("Not initialize")
          Just(x) -> x
      Just(k) ->
        k
    },
    r)
  named handle(fn(x) {r.set(Just(x));  doInit(x); () })
    fun emit(a)
      lcurrent := Just(a)
      (!pr.listeners).foreach fn(l)
        l(a)
    raw ctl yield()
      continuex := (fn() {rcontext.resume(())})
    raw ctl watch_(o, triggerImmediately)
      o.listeners.set(Cons(fn(b) {rcontext.resume(b)}, !(o.listeners)))
      if triggerImmediately then
        (o.current)()
        ()
  pr
  

fun main()
  val result = try
    val oProvider = mkProvider(
      fn(r: rref<int>) {
        r.emit(1)
        r.emit(2)
        0
      },
      fn (x: int) x.show,
      "o"
    )
    val sProvider = mkProvider(
      fn(r: rref<int>){
        trace("Hi")
        r.emit(100)
        val x = r.watch(oProvider, True)
        trace("X: " ++ x.show)
        1
      },
      fn(x:int) x.show,
      "s"
    );
    (sProvider.current)()
  match result
    Ok(x) -> x.show
    Error(e) -> e.show
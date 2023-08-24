import std/num/int32

alias providerToken = int32
struct providerBase<t>
  origin: some<h> ref<h, maybe<providerBase<t>>>
  over: some<h> ref<h, maybe<providerBase<t>>>
  token: providerToken

fun providerBase()
  val p = ProviderBase(ref(Nothing), ref(Nothing), unsafe-total{unique().int32})
  p.origin.set(Just(p))
  p.over.set(Just(p))
  p

rec type pOverride<t>
  Override
    origin: providerBase<t>
    over: providerBase<t>

struct container<h>
  // At creation time provided by users
  parent: some<h1> maybe<container<h1>> = Nothing
  overrides: list<forall<t> pOverride<t>> = []
  observers: list<observer> = []
  scheduler: scheduler<h>
  // At creation time computed properties
  depth: int32
  root: maybe<some<h1> container<h1>>
  // Comes after creation (so needs to be in ref)
  children: ref<h, list<some<h1> container<h1>>>
  stateReaders: ref<h, list<forall<t> (providerToken, stateReader<t>)>>
  overrideForProvider: ref<h, list<forall<t> pOverride<t>>>

fun createContainer(parent: some<h1> maybe<container<h1>> = Nothing, overs: list<forall<t> pOverride<t>> = [], observers: list<observer> =[])
  val c = Container(
    parent, overs, observers ++ parent.map(fn(p) container/observers(p)).default([]),
    scheduler=parent.map(fn(p) p.scheduler).default(Scheduler(ref([]), ref([]))), 
    depth=parent.map(fn(p) p.depth + 1.int32).default(0.int32),
    root=parent.map(fn(p) p.root).default(Nothing),
    overrideForProvider=ref(overs), // TODO: Fix
    children=ref([]), stateReaders=ref(
      parent.map(fn(p) (!p.stateReaders).filter(fn(e) e.snd.isDynamicallyCreated)).default([])
    ))
  match parent
    Just(p) -> p.children.set(Cons(c,!p.children)) // TODO: Override for family
    Nothing -> ()
  // val overrideReaders= overs.map(fn(o:some<t> pOverride<t>) (o.origin.token, StateReader(o.origin, ref(o.over), c, False)))
  c
  // c(stateReaders=ref(overrideReaders ++ !c.stateReaders))


struct scheduler<h>
  toDispose: ref<h, list<forall<t> providerElement<t>>>
  toRefresh: ref<h, list<forall<t> providerElement<t>>>
  // TODO: Store provider resumptions
  // TODO: Store provider subscriptions to other provider states

rec type pref<t>
  Ref
    container: some<h> container<h>

rec type provider<t>
  Provider
    create: (pref<t>) -> t
    name: string
    dependencies: list<forall<a> ref<global, provider<a>>> = []

rec type providerElement<t>
  ProviderElement
    // origin: provider<t> // Prior to overrides
    provider: provider<t>
    container: some<h1> ref<h1, container<h1>> // backref to container (container has ref via stateReader)
    // TODO: Should the element mutate refs, or should the container?
    dependents: list<some<h> ref<h, subscription<t>>> // generic subscriptions either from a container context or from a provider?
    create: () -> () // TODO: 

struct subscription<t>
  provider: providerElement<t>
  container: some<h> container<h>

struct stateReader<t>
  origin: providerBase<t>
  over: some<h> ref<h, providerBase<t>>
  container: some<h> container<h>
  isDynamicallyCreated: bool

struct observer
  onChange: forall<a> (maybe<a>, a) -> ()

alias listenable<t> = provider<t>

fun token(p: provider<t>)
  p.name

// fun read(container: container<h>, listenable: provider<r>): r
//   listenable.token.read(container)

fun hasState(container: container<h>, listenable: providerBase<r>): read<h> bool
  hasState(container, listenable.token)
  
fun hasState(container: container<h>, token: providerToken): read<h> bool
  (!container.stateReaders).any(fn((t, _)) t == token)
  
val cont = unsafe-total({createContainer()})
val prov = Provider(fn(r) 1, "foo", [])

fun main()
  // cont.hasState(prov).println
  val p = providerBase()
  p.token.show.println
rec type pOverride<t>
  Override
    token: providerToken
    create: pref<t> -> t

struct container<h>
  // At creation time
  parent: some<h1> maybe<container<h1>> = Nothing
  overrides: list<forall<t> pOverride<t>> = []
  observers: list<observer> = []
  scheduler: scheduler<h>
  // Comes after creation (so needs to be in ref)
  children: ref<h, list<some<h1> container<h1>>>
  stateReaders: ref<h, list<forall<t> (providerToken, stateReader<t>)>>

fun createContainer(parent: some<h1> maybe<container<h1>> =Nothing, overrides: list<forall<t> pOverride<t>> = [], observers: list<observer> =[])
  Container(
    parent, overrides, observers, 
    scheduler=parent.map(fn(p) p.scheduler).default(Scheduler(ref([]), ref([]))), 
    children=ref([]), stateReaders=ref([]))


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
  origin: provider<t>
  container: some<h> container<h>
  isDynamicallyCreated: bool

struct observer
  onChange: forall<a> (maybe<a>, a) -> ()

alias listenable<t> = provider<t>

alias providerToken = string
fun token(p: provider<t>)
  p.name

// fun read(container: container<h>, listenable: provider<r>): r
//   listenable.token.read(container)

fun hasState(container: container<h>, listenable: provider<r>): read<h> bool
  hasState(container, listenable.token)
  
fun hasState(container: container<h>, token: providerToken): read<h> bool
  (!container.stateReaders).any(fn((t, _)) t == token)
  
val cont = unsafe-total({createContainer()})
val prov = Provider(fn(r) 1, "foo", [])

fun main()
  cont.hasState(prov).println
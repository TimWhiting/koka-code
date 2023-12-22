pub effect acquire<e> {
    fun store-release(free : () -> e ()) : ()
}

fun run-dsl(dsl : () -> <acquire<e>|e> a, state : ref<h, list<() -> e ()>>) : <read<h>,write<h>,div|e> a {
    with fun store-release(f) {
        val r = !state
        set(state, Cons(f, r))
    }
    mask<read>(fn() { mask<write>(fn() { mask<div>(dsl) }) })
}

pub fun with-acquired(dsl : () -> acquire<e> a, inner : a -> e ()) : <div|e> () {
    run(fn() {
        val stref = ref(Nil)
        val a = mask<alloc>(fn() { run-dsl(dsl, stref) })
        mask<alloc>(fn() { mask<read>(fn() { mask<write>(fn() { mask<div>(fn() { inner(a) }) }) }) })
    })
}

fun main()
  "Hi".println
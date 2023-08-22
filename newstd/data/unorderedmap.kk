// Adapted from https://github.com/haskell-unordered-containers/unordered-containers/blob/master/Data/HashMap/Internal.hs
import std/num/int32
import newstd/data/vector

value type leaf<k,v>
  L(key: k, value: v)

type hashMapI<k,v>
  Empty
  BitmapIndexed(bitmap: int32, values: vector<hashMapI<k,v>>)
  Leaf(hash: int32, leaf: leaf<k,v>)
  Full(values: vector<hashMapI<k,v>>)
  Collision(hash: int32, values: vector<leaf<k,v>>)

pub type hashMap<k,v>
  HashMap(map: hashMapI<k,v>, eq: some<e1> (k, k) -> e1 bool, hash: some<e2> (k) -> e2 int32)

fun is-leaf-or-collision(n: hashMapI<k,v>): bool
  match n
    Leaf -> True
    Collision -> True
    _ -> False

pub fun empty(hash: some<e2> (k) -> e2 int32, eq: some<e1> (k, k) -> e1 bool): hashMap<k,v>
  HashMap(Empty, eq, hash)

pub fun singleton(k: k, v: v, hash: (k) -> e2 int32, eq: (k, k) -> e1 bool ): e2 hashMap<k,v>
  HashMap(Leaf(hash(k), L(k, v)), eq, hash)

pub fun is-null(n: hashMap<k,v>): bool
  match n
    HashMap(Empty) -> True
    _ -> False

pub fun size(h: hashMap<k,v>): int
  size(h.map)

pub fun size(h: hashMapI<k,v>): int
  match h
    Empty -> 0
    Leaf -> 1
    BitmapIndexed(_, vals) -> 
      var res := 0
      vals.foreach() fn(e)
        res := res + e.unsafe-decreasing.size
      res
    Full(vals) ->
      var res := 0
      vals.foreach() fn(e)
        res := res + e.unsafe-decreasing.size
      res
    Collision(_, vals) -> vals.length

pub fun member(h: hashMap<k,v>, k: k): e bool
  lookup(h, k).is-just

pub fun lookup(h: hashMap<k,v>, k: k): e maybe<v>
  lookupInternal(h.map, (h.hash)(k), k, zero, h.eq)

fun lookupInternal(h: hashMapI<k,v>, hash: int32, k: k, s: int32, eq: (k, k) -> e bool): e maybe<v>
  match h
    Empty -> Nothing
    Leaf(_, L(k', v)) -> if eq(k, k') then Just(v) else Nothing
    BitmapIndexed(b, vals) -> 
      val m = maskbit(hash, s)
      val child = unsafe-total{vals[b.sparseIndex(m)]}
      if b.and(m) == zero then Nothing else child.unsafe-decreasing.lookupInternal(hash, k, s.nextShift, eq)
    Full(vals) ->
      val child = unsafe-total{vals[index(hash, s)]}
      child.unsafe-decreasing.lookupInternal(hash, k, s.nextShift, eq)
    Collision(_, vals) ->
      vals.foreach-while(fn(x) if eq(x.key, k) then Just(x.value) else Nothing)

pub fun findWithDefault(h: hashMap<k,v>, k: k, def: v): v
  match lookup(h, k)
    Just(v) -> v
    Nothing -> def

fun collision(h: hashMapI<k,v>, l1: leaf<k,v>, l2: leaf<k,v>, hash: int32): hashMapI<k,v>
  Collision(hash, vector([l1, l2]))

fun bitmapIndexedOrFull(h: int32, a: vector<hashMapI<k,v>>): hashMapI<k,v>
  if h == fullBitmap then Full(a) else BitmapIndexed(h, a)

// TODO: Fix for update vector instead of assign
pub fun insert(h: hashMap<k,v>, k: k, v: v): e hashMap<k,v>
  h(map=insertInternal(h.map, (h.hash)(k), k, v, zero, h.eq))

fun insertInternal(h: hashMapI<k,v>, hash: int32, k: k, v: v, s: int32, eq: (k, k) -> e bool): e hashMapI<k,v>
  match h
    Empty -> Leaf(hash, L(k, v))
    Leaf(hash2, l) ->
      if hash == hash2 then
        if eq(k, l.key) then
          if unsafePtrEq(v, l.value) then
            h
          else
            Leaf(hash, L(k, v))
        else collision(h, l, L(k, v), hash)
      else
        two(s, hash, k, v, hash2, h)
    BitmapIndexed(b, vals) ->
      val m = maskbit(hash, s)
      val i = b.sparseIndex(m)
      if b.and(m) == zero then
        vals.unsafe-assign(i.ssize_t, Leaf(hash, L(k, v)))
        bitmapIndexedOrFull(b.or(m), vals)
      else
        val old = unsafe-total{vals[i]}
        val new = old.unsafe-decreasing.insertInternal(hash, k, v, s.nextShift, eq)
        if old.unsafePtrEq(new) then
          old
        else
          vals.unsafe-assign(i.ssize_t, new)
          BitmapIndexed(b, vals)
    Full(vals) ->
      val old = unsafe-total{vals[index(hash, s)]}
      val new = old.unsafe-decreasing.insertInternal(hash, k, v, s.nextShift, eq)
      if old.unsafePtrEq(new) then
        old
      else
        vals.unsafe-assign(index(hash, s).ssize_t, new)
        Full(vals)
    Collision(h', vals) ->
      if h' == hash then
        val newVals = vals.updateOrPush(fn(e) eq(e.key, k)) fn(e)
          match e
            Just(L(k', _)) -> L(k', v)
            _ -> L(k, v)
        Collision(hash, newVals)
      else
        BitmapIndexed(maskbit(hash, s), [h].vector).unsafe-decreasing.insertInternal(hash, k, v, s, eq)

pub fun insertWith(h: hashMap<k,v>, k: k, v: v, update: (v) -> v): e hashMap<k,v>
  h(map=insertUpdateInternal(h.map, (h.hash)(k), k, v, fn (old, new) update(old), zero, h.eq))

pub fun insertModifying(h: hashMap<k,v>, k: k, v: v, update: (v, v) -> v): e hashMap<k,v>
  h(map=insertUpdateInternal(h.map, (h.hash)(k), k, v, update, zero, h.eq))

fun insertUpdateInternal(h: hashMapI<k,v>, hash: int32, k: k, v: v, update: (v, v) -> v, s: int32, eq: (k, k) -> e bool): e hashMapI<k,v>
  match h
    Empty -> Leaf(hash, L(k, v))
    Leaf(hash2, l) ->
      if hash == hash2 then
        if eq(k, l.key) then
          Leaf(hash, L(k, update(l.value, v)))
        else collision(h, l, L(k, update(l.value, v)), hash)
      else
        two(s, hash, k, v, hash2, h)
    BitmapIndexed(b, vals) ->
      val m = maskbit(hash, s)
      val i = b.sparseIndex(m)
      if b.and(m) == zero then
        vals.unsafe-assign(i.ssize_t, Leaf(hash, L(k, v)))
        bitmapIndexedOrFull(b.or(m), vals)
      else
        val old = unsafe-total{vals[i]}
        val new = old.unsafe-decreasing.insertUpdateInternal(hash, k, v, update, s.nextShift, eq)
        if old.unsafePtrEq(new) then
          old
        else
          vals.unsafe-assign(i.ssize_t, new)
          BitmapIndexed(b, vals)
    Full(vals) ->
      val old = unsafe-total{vals[index(hash, s)]}
      val new = old.unsafe-decreasing.insertUpdateInternal(hash, k, v, update, s.nextShift, eq)
      if old.unsafePtrEq(new) then
        old
      else
        vals.unsafe-assign(index(hash, s).ssize_t, new)
        Full(vals)
    Collision(h', vals) ->
      if h' == hash then
        val newVals = vals.updateOrPush(fn(e) eq(e.key, k)) fn(e)
          match e
            Just(L(k', v')) -> L(k', update(v', v))
            _ -> L(k, v)
        Collision(hash, newVals)
      else
        BitmapIndexed(maskbit(hash, s), [h].vector).unsafe-decreasing.insertUpdateInternal(hash, k, v, update, s, eq)

fun two(s: int32, h1: int32, k1: k, v1: v, h2: int32, t2: hashMapI<k,v>): hashMapI<k,v>
  val bp1 = h1.maskbit(s)
  val bp2 = h2.maskbit(s)
  val i1 = h1.index(s)
  val i2 = h2.index(s)
  val idx2 = i1 < i2
  fun go(s', h1', k1', v1', h2', t2')
    if bp1 == bp2 then
      val st = go(s.nextShift.unsafe-decreasing, h1', k1', v1', h2', t2')
      val ary = vector([st])
      BitmapIndexed(bp1, ary)
    else
      val ary = vector([Leaf(h1', L(k1', v1')), t2'])
      BitmapIndexed(bp1.or(bp2), ary)
  go(s, h1, k1, v1, h2, t2)

val maxChildren = one.shl(bitsPerSubkey)
val bitsPerSubkey = 5
val bitsPerSubkey32 = bitsPerSubkey.int32
val bitMask = one.shl(bitsPerSubkey - 1)

fun index(bitmap: int32, shift: int32): int
  bitmap.shr(shift.int).and(bitMask).int

fun maskbit(bitmap: int32, shift: int32): int32
  one.shl(index(bitmap, shift))

fun sparseIndex(bitmap: int32, shift: int32): int
  bitmap.and(shift - one).popcount

val fullBitmap = zero.not.shl(maxChildren.int).not

fun nextShift(s: int32): int32
  s + bitsPerSubkey32

// Can give false negatives due to value structs
extern unsafePtrEq(a: a, b: a): bool
  c inline "&#1 == &#2"
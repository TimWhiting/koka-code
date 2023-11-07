import boundaries
value struct range<v>
  lower: boundary<v>
  upper: boundary<v>

// TODO: 

// The empty range
val emptyRange = Range(BoundaryAboveAll, BoundaryBelowAll)

// The full range
val fullRange = Range(BoundaryBelowAll, BoundaryAboveAll)

// A range containing a single value
fun singletonRange(v: v): range<v>
  Range(BoundaryBelow(v), BoundaryAbove(v))

// If the range is a singleton, return Just the value. Otherwise return nothing
// Known bug: This always returns nothing for ranges including BoundaryBelowAll or BoundaryAboveAll.
//   For bounded types this can be incorrect.
fun rangeSingletonValue(r: range<v>, adjacent: (v, v) -> e bool, adjacentBelow: v -> e v, (==): (v, v) -> e bool): e maybe<v>
  match r
    Range(BoundaryBelow(v1), BoundaryBelow(v2)) ->
      if adjacent(v1, v2) then Just(v1) else Nothing
    Range(BoundaryBelow(v1), BoundaryAbove(v2)) ->
      if v1 == v2 then Just(v1) else Nothing
    Range(BoundaryAbove(v1), BoundaryBelow(v2)) ->
      val v2' = v2.adjacentBelow
      val v2'' = v2.adjacentBelow 
      if v1 == v2'' then Just(v2') else  Nothing
    Range(BoundaryAbove(v1), BoundaryAbove(v2)) ->
      if adjacent(v1, v2) then Just(v2) else Nothing
    _ -> Nothing

// A range is empty unless its lower boundary is less than its upper boundary
fun isEmpty(r: range<v>, compare: (boundary<v>, boundary<v>) -> e order): e bool
  match compare(r.lower, r.upper)
    Lt -> False
    _ -> True

// A range is full if it contains every possible value
fun rangeIsFull(r: range<v>)
  r.lower.is-boundaryBelowAll && r.upper.is-boundaryAboveAll

// Two ranges overlap if their intersection is not empty




// TODO: 
import ranges
import boundaries

struct rangeSet<v>
  ranges: list<range<v>>


fun rSingleton(v: v): rangeSet<v>
  RangeSet([v.singletonRange])

fun is-empty(r: rangeSet<v>): bool
  r.ranges.is-empty

// TODO: 

// The empty set
val rSetEmpty = RangeSet([])

// The set that contains everything
val rSetFull = RangeSet([Range(BoundaryBelowAll, BoundaryAboveAll)])

// Construct a range set
// TODO:
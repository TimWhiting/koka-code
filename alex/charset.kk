import alex/data/rangedset
alias byte = int8
alias charset = rangeSet<char>
alias byteset = rangeSet<byte>
alias utf8range = span<(byte, list<byte>)>
type encoding
  Latin1
  Utf8

val emptyCharSet = rSetEmpty

alias span<a> = (a, a) // Lower bound inclusive, higher bound exclusive
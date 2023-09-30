import compiler/common/id

// Pretty print environment for types
struct prettyTypeEnv
  showKinds: bool = False
  showIds: bool = False // show id numbers
  expandSynonyms: bool = False
  colors: colorScheme = ColorScheme()
  nice: nice

effect prettyTypeEff
  val prettyTypeEnv: prettyTypeEnv
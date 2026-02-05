/-!
# English Predicates

Re-exports verbal and adjectival predicate entries.
-/

import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival

namespace Fragments.English.Predicates

export Verbal (
  -- Types
  VerbClass PresupTriggerType ComplementType ThetaRole ControlType VerbEntry
  PreferentialBuilder
  -- Functions
  getCoSSemantics presupposesComplement isPresupTrigger
  isPreferentialAttitude
  allVerbs
  toWord3sg toWordBase
)

export Adjectival (
  AdjectivalPredicateEntry
  allEntries
)

end Fragments.English.Predicates

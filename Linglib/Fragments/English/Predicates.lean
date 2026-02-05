import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival

/-!
# English Predicates

Re-exports verbal and adjectival predicate entries.
-/

namespace Fragments.English.Predicates

export Verbal (
  -- Types
  VerbClass PresupTriggerType ComplementType ThetaRole ControlType VerbEntry
  PreferentialBuilder
  -- Functions
  getCoSSemantics presupposesComplement isPresupTrigger
  isPreferentialAttitude
  allVerbs
)

export Adjectival (
  AdjectivalPredicateEntry
  allEntries
)

end Fragments.English.Predicates

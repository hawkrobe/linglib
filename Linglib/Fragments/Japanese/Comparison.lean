import Linglib.Core.Case.ComparativeEntry

/-!
# Japanese Comparative Construction @cite{stassen-1985}

Japanese uses a **separative** comparative construction: the standard NP is
marked with the postposition *yori* ('from/than'), which has ablative
semantics. The adjective appears in its bare (positive) form with no
comparative morphology.

Example: *Taroo wa Hanako yori se ga takai*
         'Taro TOP Hanako from height NOM tall'
         = 'Taro is taller than Hanako'

The marker *yori* is etymologically and synchronically a separative/ablative
postposition, also used in spatial 'from' contexts. This exemplifies
@cite{stassen-1985}'s localistic hypothesis: comparative markers are borrowed
from spatial case morphology.
-/

namespace Fragments.Japanese.Comparison

/-- Japanese comparative: separative (ablative) standard marker *yori*. -/
def entry : Core.ComparativeEntry :=
  { standardCase := .abl
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardMarker := "yori"
  , hasDegreeMorphology := false }

-- Per-datum verification
theorem standard_is_ablative : entry.standardCase = .abl := rfl
theorem case_is_fixed : entry.caseAssignment = .fixed := rfl
theorem encoding_is_adverbial : entry.fixedEncoding = some .adverbial := rfl
theorem no_degree_morphology : entry.hasDegreeMorphology = false := rfl

end Fragments.Japanese.Comparison

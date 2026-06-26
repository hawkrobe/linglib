import Linglib.Features.Case.Basic
import Linglib.Syntax.Comparative
import Linglib.Syntax.Comparative
/-!
# Japanese Comparative Construction [stassen-1985]

Japanese uses a **separative** comparative construction: the standard NP is
marked with the postposition *yori* ('from/than'), which has ablative
semantics. The adjective appears in its bare (positive) form with no
comparative morphology.

Example: *Taroo wa Hanako yori se ga takai*
         'Taro TOP Hanako from height NOM tall'
         = 'Taro is taller than Hanako'

The marker *yori* is etymologically and synchronically a separative/ablative
postposition, also used in spatial 'from' contexts. This exemplifies
[stassen-1985]'s localistic hypothesis: comparative markers are borrowed
from spatial case morphology.
-/

namespace Japanese.Comparison

/-- Japanese comparative: separative (ablative) standard marker *yori*. -/
def entry : Comparative.ComparativeEntry :=
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

-- ============================================================================
-- ComparativeProfile bundle (consumed by Studies/Stassen2013.lean)
-- ============================================================================

/-- Japanese comparative profile (WALS Ch 121 + degree-word + superlative). -/
def comparison : Comparative.ComparativeProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , comparativeType := .locational
  , degreeWord := .noDegreeMarking
  , superlative := .comparativeUniversal
  , comparativeForm := "Y yori X ga Adj"
  , standardMarker := "yori"
  , degreeMarker := ""
  , basicOrder := "SOV" }

end Japanese.Comparison

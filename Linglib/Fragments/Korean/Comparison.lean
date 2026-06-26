import Linglib.Features.Case.Basic
import Linglib.Syntax.Comparative
import Linglib.Syntax.Comparative
/-!
# Korean Comparative Construction [stassen-1985]

Korean uses a **separative** comparative construction: the standard NP is
marked with the postposition *-boda* ('from/than'), which has ablative
semantics. The adjective appears in its bare form with no comparative
morphology; the optional adverb *deo* ('more') may intensify.

Example: *Yenghi-ga Chelswu-boda (deo) khu-da*
         'Yenghi-NOM Chelswu-than (more) tall-DECL'
         = 'Yenghi is taller than Chelswu'

The marker *-boda* is sometimes analyzed as a particle rather than a case
marker, but its ablative/separative semantics ('from the point of view of')
places Korean firmly in the separative class in [stassen-1985]'s
typology.
-/

namespace Korean.Comparison

/-- Korean comparative: separative standard marker *-boda*. -/
def entry : Comparative.ComparativeEntry :=
  { standardCase := .abl
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardMarker := "-boda"
  , hasDegreeMorphology := false }

-- Per-datum verification
theorem standard_is_ablative : entry.standardCase = .abl := rfl
theorem case_is_fixed : entry.caseAssignment = .fixed := rfl
theorem encoding_is_adverbial : entry.fixedEncoding = some .adverbial := rfl
theorem no_degree_morphology : entry.hasDegreeMorphology = false := rfl

-- ============================================================================
-- ComparativeProfile bundle (consumed by Studies/Stassen2013.lean)
-- ============================================================================

/-- Korean comparative profile (WALS Ch 121 + degree-word + superlative). -/
def comparison : Comparative.ComparativeProfile :=
  { language := "Korean"
  , iso := "kor"
  , comparativeType := .locational
  , degreeWord := .noDegreeMarking
  , superlative := .comparativeUniversal
  , comparativeForm := "Y-boda X-ga Adj"
  , standardMarker := "-boda"
  , degreeMarker := ""
  , basicOrder := "SOV" }

end Korean.Comparison

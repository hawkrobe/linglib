import Linglib.Core.Case

/-!
# Turkish Comparative Construction @cite{stassen-1985}

Turkish uses a **separative** comparative construction: the standard NP is
marked with the ablative suffix `-dan`/`-den` (subject to vowel harmony). The
adjective appears in its bare (positive) form with no comparative morphology.

Example: *Ali Veli-den (daha) uzun*
         'Ali Veli-ABL (more) tall'
         = 'Ali is taller than Veli'

The ablative case suffix `-dan`/`-den` is the same morpheme used for spatial
'from' (*İstanbul'dan* 'from Istanbul'), exemplifying @cite{stassen-1985}'s
localistic hypothesis: comparative markers derive from spatial case morphology.
The optional adverb *daha* ('more') may intensify but is not required.
-/

namespace Fragments.Turkish.Comparison

/-- Turkish comparative: separative (ablative) standard marker `-dan`/`-den`. -/
def entry : Core.ComparativeEntry :=
  { standardCase := .abl
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardMarker := "-dan/-den"
  , hasDegreeMorphology := false }

-- Per-datum verification
theorem standard_is_ablative : entry.standardCase = .abl := rfl
theorem case_is_fixed : entry.caseAssignment = .fixed := rfl
theorem encoding_is_adverbial : entry.fixedEncoding = some .adverbial := rfl
theorem no_degree_morphology : entry.hasDegreeMorphology = false := rfl

end Fragments.Turkish.Comparison

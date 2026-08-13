import Linglib.Features.Case.Basic
import Linglib.Syntax.Comparative

/-!
# Turkish Comparative Construction [stassen-1985]

Turkish uses a **separative** comparative construction: the standard NP is
marked with the ablative suffix `-dan`/`-den` (subject to vowel harmony). The
adjective appears in its bare (positive) form with no comparative morphology.

Example: *Ali Veli-den (daha) uzun*
         'Ali Veli-ABL (more) tall'
         = 'Ali is taller than Veli'

The ablative case suffix `-dan`/`-den` is the same morpheme used for spatial
'from' (*İstanbul'dan* 'from Istanbul'), exemplifying [stassen-1985]'s
localistic hypothesis: comparative markers derive from spatial case morphology.
The optional adverb *daha* ('more') may intensify but is not required. No
superlative strategy is recorded: the free superlative word *en* fits none of
`SuperlativeStrategy`'s cases.
-/

set_option autoImplicit false

namespace Turkish.Comparison

open Comparative

/-- The separative (ablative) standard marker, subject to vowel harmony. -/
def standardMarker : String := "-dan/-den"

/-- Turkish comparative: separative (ablative) standard marker `-dan`/`-den`. -/
def entry : ComparativeEntry :=
  { standardCase := .abl
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardMarker := standardMarker
  , hasDegreeMorphology := false }

-- Per-datum verification
theorem standard_is_ablative : entry.standardCase = .abl := rfl
theorem case_is_fixed : entry.caseAssignment = .fixed := rfl
theorem encoding_is_adverbial : entry.fixedEncoding = some .adverbial := rfl
theorem no_degree_morphology : entry.hasDegreeMorphology = false := rfl

/-! ### WALS Ch 121 classification data -/

/-- Optional free degree word *daha*; the adjective itself carries no
    comparative morphology (`entry.hasDegreeMorphology = false`). -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Illustrative comparative. -/
def comparativeForm : String := "X Y-den daha Adj"

/-- The optional free degree word. -/
def degreeMarker : String := "daha"

end Turkish.Comparison

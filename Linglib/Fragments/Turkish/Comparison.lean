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

/-- The ablative comparative: `-dan`/`-den`-marked standard, optional free
    *daha*, no degree morphology. -/
def dan : Comparative :=
  { standardMarker := some "-dan/-den"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl
  , degreeMarker := some "daha" }

/-- Optional free degree word *daha*; the adjective itself carries no
    comparative morphology. -/
def degreeWord : DegreeWordType := .hasDegreeWord

end Turkish.Comparison

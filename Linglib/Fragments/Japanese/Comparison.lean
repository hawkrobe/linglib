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

set_option autoImplicit false

namespace Japanese.Comparison

open Comparative

/-- The *yori*-comparative: separative (ablative) postposition-marked
    standard, no degree morphology. -/
def yori : Comparative :=
  { standardMarker := some "yori"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl }

/-- No overt degree marking. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative as comparative with universal standard (*dare yori mo*). -/
def superlative : SuperlativeStrategy := .comparativeUniversal

end Japanese.Comparison

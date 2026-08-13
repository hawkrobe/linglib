import Linglib.Features.Case.Basic
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

/-- The separative (ablative) standard marker. -/
def standardMarker : String := "yori"

/-- Japanese comparative: separative (ablative) standard marker *yori*. -/
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

/-- No overt degree marking. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative as comparative with universal standard (*dare yori mo*). -/
def superlative : SuperlativeStrategy := .comparativeUniversal

/-- Illustrative comparative. -/
def comparativeForm : String := "Y yori X ga Adj"

end Japanese.Comparison

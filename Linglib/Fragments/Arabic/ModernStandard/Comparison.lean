import Linglib.Syntax.Comparative

/-!
# Modern Standard Arabic comparative data

MSA compares with *X ʔafʕal min Y*: the separative preposition *min* 'from'
marks the standard (WALS Ch 121A: locational, [stassen-2013]) and the elative
pattern *ʔafʕal* carries the comparison, with no separate degree word.
Superlative via the elative without a comparison standard.
-/

set_option autoImplicit false

namespace Arabic.ModernStandard.Comparison

open Comparative

/-- The *min*-comparative: separative preposition-marked standard. -/
def min : Comparative :=
  { standardMarker := some "min"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl }

/-- The elative pattern carries comparison; no separate degree word. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Elative superlative. -/
def superlative : SuperlativeStrategy := .elative

end Arabic.ModernStandard.Comparison

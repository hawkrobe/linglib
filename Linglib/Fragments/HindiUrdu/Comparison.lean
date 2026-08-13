import Linglib.Syntax.Comparative

/-!
# Hindi-Urdu comparative data

Hindi-Urdu compares with *X Y se (zyaadaa) Adj hai*: the ablative postposition
*se* 'from' marks the standard (WALS Ch 121A: locational, [stassen-2013]), and
the free degree word *zyaadaa* 'more' is optional. Superlative via comparative
with a universal standard (*sab se* 'than all').
-/

set_option autoImplicit false

namespace HindiUrdu.Comparison

open Comparative

/-- The *se*-comparative: separative postposition-marked standard. -/
def se : Comparative :=
  { standardMarker := some "se"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl
  , degreeMarker := some "zyaadaa" }

/-- Optional free degree word *zyaadaa*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Superlative as comparative with universal standard (*sab se*). -/
def superlative : SuperlativeStrategy := .comparativeUniversal

end HindiUrdu.Comparison

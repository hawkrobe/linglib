import Linglib.Syntax.Comparative

/-!
# Latin comparative data

Latin has two productive comparative constructions: *X Adj-ior quam Y* with
the particle *quam*, and *X Adj-ior Y-ABL* with a bare ablative standard —
[stassen-1985] classifies Latin as particle-primary, separative-secondary.
Latin is uncoded in WALS Ch 121A; each construction's type is derived from
its anatomy (`quam.type`, `ablative.type`). Degree is marked by the bound
affix *-ior*; the superlative is morphological.
-/

set_option autoImplicit false

namespace Latin.Comparison

open Comparative

/-- The *quam*-comparative: the primary, particle-marked construction. -/
def quam : Comparative :=
  { standardMarker := some "quam"
  , caseAssignment := .derived
  , degreeMarker := some "-ior"
  , degreeMorphology := true }

/-- The bare-ablative comparative: no segmental marker, ablative standard. -/
def ablative : Comparative :=
  { caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl
  , degreeMarker := some "-ior"
  , degreeMorphology := true }

/-- Bound comparative affix *-ior*. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative. -/
def superlative : SuperlativeStrategy := .morphological

end Latin.Comparison

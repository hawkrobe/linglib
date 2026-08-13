import Linglib.Syntax.Comparative

/-!
# Finnish comparative data

Finnish compares with *X on Adj-mpi kuin Y*: the particle *kuin* marks the
standard (WALS Ch 121A: particle, [stassen-2013]), with a secondary
separative option marking the standard with the partitive instead —
[stassen-1985] classifies Finnish as particle-primary, separative-secondary.
Degree is marked by the bound affix *-mpi*; the superlative is morphological.
-/

set_option autoImplicit false

namespace Finnish.Comparison

open Comparative

/-- The *kuin*-comparative: the primary, particle-marked construction. -/
def kuin : Comparative :=
  { standardMarker := some "kuin"
  , caseAssignment := .derived
  , degreeMarker := some "-mpi"
  , degreeMorphology := true }

/-- The secondary separative construction: partitive-marked standard. -/
def partitive : Comparative :=
  { caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .part
  , degreeMarker := some "-mpi"
  , degreeMorphology := true }

/-- Bound comparative affix *-mpi*. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative. -/
def superlative : SuperlativeStrategy := .morphological

end Finnish.Comparison

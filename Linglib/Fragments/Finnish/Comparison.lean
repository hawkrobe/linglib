import Linglib.Syntax.Comparative

/-!
# Finnish comparative data

Finnish marks the standard of comparison with the particle *kuin* (WALS Ch 121A:
particle, [stassen-2013]); [stassen-1985] classifies Finnish as particle-primary
with a secondary separative option (partitive-marked standard). Degree is marked
by the bound affix *-mpi*, and the superlative is morphological.
-/

set_option autoImplicit false

namespace Finnish.Comparison

open Comparative

/-- Bound comparative affix *-mpi*. -/
def degreeWord : DegreeWordType := .morphological

/-- Morphological superlative. -/
def superlative : SuperlativeStrategy := .morphological

/-- Illustrative comparative (particle strategy; the secondary separative
    option marks the standard with the partitive instead). -/
def comparativeForm : String := "X on Adj-mpi kuin Y"

/-- The comparative particle; the partitive-marked standard is the secondary
    separative option. -/
def standardMarker : String := "kuin"

/-- The bound comparative affix. -/
def degreeMarker : String := "-mpi"

end Finnish.Comparison

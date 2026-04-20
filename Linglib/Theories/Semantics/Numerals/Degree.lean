import Linglib.Core.Scales.Scale

/-!
# Numeral Semantics over `HasDegree`

@cite{kennedy-2007} @cite{schwarzschild-2005}

Generic numeral predicates parameterized by the `Core.Scale.HasDegree`
typeclass — applicable to any entity type carrying a measure into a totally
ordered codomain. The `Nat` → ℚ instance for cardinalities lives here so
this file is self-contained for callers that just want "compare a stated
numeral against an entity's measured degree".

The `Nat → Nat → Prop` numeral meanings (Kennedy/Horn `bareMeaning`,
`atLeastMeaning`, …) live in `Basic.lean`; this file is the degree-typed
counterpart for measurement domains (cost, height, weight, …).
-/

namespace Semantics.Numerals

open Core.Scale

/-- Cardinality (`Nat`) participates in the `HasDegree` framework via the
    canonical embedding into ℚ. -/
instance CardinalityDegree : HasDegree Nat ℚ where
  degree := λ n => (n : ℚ)

/-- Literal/exact numeral semantics over `HasDegree`. "Six feet" is true of
    `x` iff `μ_height(x) = 6`. -/
def numeralExact {E α : Type} [HasDegree E α] [BEq α]
    (stated : α) (entity : E) : Bool :=
  HasDegree.degree entity == stated

end Semantics.Numerals

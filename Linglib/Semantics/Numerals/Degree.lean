import Linglib.Semantics.Degree.HasMeasure

/-!
# Numeral Semantics over `HasMeasure`

[kennedy-2007] [schwarzschild-2005]

Generic numeral predicates parameterized by the `Semantics.Degree.HasMeasure`
typeclass — applicable to any entity type carrying a measure into a totally
ordered codomain. The `Nat` → ℚ instance for cardinalities lives here so
this file is self-contained for callers that just want "compare a stated
numeral against an entity's measured degree".

The `Nat → Nat → Prop` numeral meanings (Kennedy/Horn `bareMeaning`,
`atLeastMeaning`, …) live in `Basic.lean`; this file is the degree-typed
counterpart for measurement domains (cost, height, weight, …).
-/

namespace Semantics.Numerals

open Semantics.Degree
/-- Cardinality (`Nat`) participates in the `HasMeasure`/`HasMeasure` framework
    via the canonical embedding into ℚ. -/
instance CardinalityDegree : HasMeasure Nat ℚ where
  degree := λ n => (n : ℚ)

end Semantics.Numerals

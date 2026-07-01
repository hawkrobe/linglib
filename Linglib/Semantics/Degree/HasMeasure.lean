import Linglib.Semantics.Degree.Defs

/-!
# HasMeasure — the measurement typeclass

`HasMeasure E α` is the formal-semantics measure function `μ : E → α`, parameterized
over both the entity type `E` and the codomain scale `α`. This file adds only the
abstract typeclass; the concrete scale carriers `Degree`/`Threshold` are defined in
`Defs.lean`, re-exported here (via the import) so both are reachable together.

**No `outParam` on `α`**: multi-dim same-carrier measurement (e.g. an `Entity`
measured by BOTH height and weight) is supported by distinct `(E, α)` instances or
newtype wrappers (mathlib `Additive`/`Multiplicative` precedent). When an `Entity` has
multiple measures, consumers disambiguate via explicit `(α := …)` or named instances.
-/

namespace Semantics.Degree

/-- Typeclass for entities that carry a measurement on some scale — the
    formal-semantics measure function `μ : E → α`.

    The codomain `α` is polymorphic: heights might use `ℚ` (cm, exact) or `ℝ`,
    durations `ℕ` (ticks), prices `ℚ` (USD), etc. -/
class HasMeasure (E : Type*) (α : Type*) where
  degree : E → α

/-- Readable name for the measurement function, aliased to the field `degree`. -/
abbrev HasMeasure.measure {E α : Type*} [HasMeasure E α] : E → α :=
  HasMeasure.degree

end Semantics.Degree

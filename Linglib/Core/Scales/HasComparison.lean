import Mathlib.Order.Basic
import Linglib.Core.Scales.HasMeasure
import Linglib.Core.Scales.Comparison

/-!
# Core/Scales/HasComparison.lean — primitive comparison typeclass

`HasComparison α` provides a binary comparison primitive `comparativeGreater :
α → α → Prop` — "a is more-Adj than b". Lawless: anyone instantiates
(Klein delineation, Kennedy measure-derived, Charlow-Sutton-Wechsler states,
Lassiter-Goodman expected-value, Tversky-Fishburn intransitive majority).

Lawfulness is opt-in via `LawfulComparison` mixin in `LawfulComparison.lean`.

Mathlib analog: `class LT (α : Type*) where lt : α → α → Prop`.

This file is part of the Phase A.7 atomic typeclass landing per master plan v4.

## Smart constructor (NOT auto-instance)

`HasComparison.ofMeasure` is a **`def`**, not an auto-`instance`. Frameworks
opt-in via `attribute [instance] HasComparison.ofMeasure` per their carrier.
This avoids typeclass-synthesis ambiguity from the deliberate absence of
`outParam` on `HasMeasure δ` (multi-dim same-carrier support).
-/

namespace Core.Scale

/-- A type carries a binary comparison: "a is more-Adj than b". -/
class HasComparison (α : Type*) where
  comparativeGreater : α → α → Prop

/-- Smart constructor: any type with a measure into an ordered codomain
    has comparison. NOT an auto-instance (synthesis ambiguity from no
    `outParam` on δ). Frameworks opt-in via `attribute [instance]`.

    Example use: `attribute [instance] HasComparison.ofMeasure`
    inside a Kennedy-framework file scoped where δ is determinate.

    Named instance argument `m` to avoid typeclass-synthesis ambiguity
    in the body (we'd otherwise need to specify `(α := δ)` for
    `HasMeasure.measure`). `@[reducible]` is required for class-type
    `def`s (Lean elaboration hygiene). -/
@[reducible]
def HasComparison.ofMeasure {α δ : Type*} [Preorder δ] (m : HasMeasure α δ) :
    HasComparison α where
  comparativeGreater a b := Comparison.gt.rel (m.degree a) (m.degree b)

end Core.Scale

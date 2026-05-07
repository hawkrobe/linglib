import Mathlib.Order.Basic
import Mathlib.Order.RelClasses
import Linglib.Core.Scales.HasComparison

/-!
# Core/Scales/LawfulComparison.lean — opt-in lawfulness mixins

Mixin Prop typeclasses for comparison lawfulness. Each framework picks which
laws it satisfies:

- Kennedy → `TotalComparison` (linear measure)
- Klein → `LawfulComparison` only when `IsMonotoneDelineation` holds
- Charlow-Sutton-Wechsler StatesBased → `LawfulComparison`
- Lassiter-Goodman → `LawfulComparison` (transitive expected-value)
- MajorityComparison (Tversky/Fishburn) → ONLY `HasComparison` (intransitive)

The mixin pattern (`class X [HasComparison α] : Prop`) avoids diamond
inheritance from `extends HasComparison`. Mathlib analogs:
`IsCommutative`, `IsAntisymm`, `CovariantClass` — all detached
laws-as-Props.

This file is part of the Phase A.7 atomic typeclass landing per master plan v4.

## Reuses mathlib `IsStrictOrder`

Rather than reinventing `irrefl`/`trans`/`asymm` fields, `LawfulComparison`
extends mathlib's `IsStrictOrder` over `HasComparison.comparativeGreater`.
-/

namespace Core.Scale

/-- Comparison is a strict order. Mixin Prop class — laws ABOUT an existing
    `HasComparison` instance, not bundled WITH it.

    Reuses mathlib's `IsStrictOrder` to avoid duplicating
    irreflexive/transitive/asymmetric fields. -/
class LawfulComparison (α : Type*) [HasComparison α] : Prop where
  isStrictOrder : IsStrictOrder α HasComparison.comparativeGreater

/-- Comparison is total (every pair is comparable). For Kennedy-style linear
    measures. NOT satisfied by Klein nonlinear (clever) or by Lassiter
    smooth-threshold posteriors. -/
class TotalComparison (α : Type*) [HasComparison α] : Prop extends LawfulComparison α where
  total : ∀ a b : α, HasComparison.comparativeGreater a b ∨ a = b ∨
                     HasComparison.comparativeGreater b a

end Core.Scale

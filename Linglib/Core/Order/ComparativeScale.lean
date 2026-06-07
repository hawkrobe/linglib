import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Linglib.Core.Order.Boundedness

/-!
# Core/Scales/Comparative.lean — ComparativeScale + AdditiveScale
[krantz-1971] [holliday-icard-2013]

Root algebraic structures for the category of scales.

`ComparativeScale α` — a preorder with boundedness classification.
All scale-based reasoning factors through this structure.

`AdditiveScale α` — comparative scale enriched with join and finite
additivity (FA). Two independent linglib instances:
- Mereological: `ExtMeasure.additive`
- Epistemic: `EpistemicSystemFA` + `FinAddMeasure` ([holliday-icard-2013])

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).
-/

namespace Core.Order

-- ════════════════════════════════════════════════════
-- § 1c. Comparative Scale (Root Algebraic Structure)
-- ════════════════════════════════════════════════════

/-- A comparative scale: a boundedness classification on a preorder.
    This is the root object in the category of scales. All scale-based
    reasoning in linglib (degree semantics, mereological measurement,
    epistemic comparison) factors through this structure.

    The ordering comes from the ambient `[Preorder α]` — no redundant
    `le`/`le_refl`/`le_trans` fields. Morphisms are Mathlib's `Monotone`.

    [krantz-1971]: a comparative scale is an ordered set with
    enough structure to support qualitative comparison. -/
structure ComparativeScale (α : Type*) [Preorder α] where
  /-- Scale boundedness classification -/
  boundedness : Boundedness

/-- An additive scale: a comparative scale enriched with join and finite
    additivity (FA). Two independent instances exist in linglib:
    - Mereological: `ExtMeasure.additive`
    - Epistemic: probability FA

    The FA axiom says disjoint augmentation preserves order: if z is
    disjoint from both x and y, then x ≤ y ↔ x ⊔ z ≤ y ⊔ z. This
    is the qualitative content of additive representation. -/
structure AdditiveScale (α : Type*) [SemilatticeSup α] extends ComparativeScale α where
  /-- Disjointness predicate -/
  disjoint : α → α → Prop
  /-- Finite additivity: disjoint augmentation preserves order.
      Both `≤` and `⊔` come from the ambient `SemilatticeSup`. -/
  fa : ∀ (x y z : α), disjoint x z → disjoint y z →
    (x ≤ y ↔ x ⊔ z ≤ y ⊔ z)

namespace ComparativeScale

/-- Licensing prediction from the underlying boundedness. -/
def isLicensed {α : Type*} [Preorder α] (S : ComparativeScale α) : Bool :=
  S.boundedness.isLicensed

end ComparativeScale

end Core.Order

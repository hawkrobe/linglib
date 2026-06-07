import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Pullback Preorders

A `PullbackPreorder Carrier Target` is a `Preorder Carrier` realized as
the pullback of a `Preorder Target` through a projection
`proj : Carrier → Target`. The induced order is
`a ≤ a' ↔ proj a ≤ proj a'`.

This is mathlib's `Preorder.lift` packaged with the witnessing
projection and decidability of `≤`. It is the common pattern behind
several constructions in linglib:

- `Core.Order.SatisfactionOrdering α Criterion` — the projection is the
  satisfied criterion set, the target is `(Finset Criterion)ᵒᵈ` (or
  equivalently, the violated set with standard ⊆).
- `Phonology.Constraint.ConstraintSystem.paretoPullbackPreorder` — the
  projection is the score vector, the target is `Profile β n` with
  pointwise ≤.
- `Semantics.Modality.Kratzer.worldOrdering` — the projection is the
  satisfied proposition set, same shape as `SatisfactionOrdering`.
- `BundleLike.subsumptionPreorder` — the projection is a feature
  bundle's valuation, the target is `Features.Bundle` with subsumption.

## The reusable theorem

`coarsen_via_monotone` states that a monotone map `φ : F1 → F2` between
targets lifts dominance under the finer projection to dominance under
the coarser one, provided `o2.proj = φ ∘ o1.proj`. This is the schema
underlying "Pareto-on-violations ⇒ Pareto-on-satisfaction" and any
other forgetful coarsening between qualitatively-comparable
representations.
-/

namespace Core.Order

/-- A preorder on `Carrier` realized as the pullback of a
    `Preorder Target` through `proj : Carrier → Target`.

    `extends Preorder Carrier`, so all of mathlib's order vocabulary
    (`≤`, `<`, `Maximal`, `IsMax`) is available; `proj`/`decLE` expose
    the construction data. `le_iff_proj` is the load-bearing coherence
    field — the bundled `≤` agrees with the projection pullback. -/
structure PullbackPreorder (Carrier : Type*) (Target : Type*) [Preorder Target]
    extends Preorder Carrier where
  proj : Carrier → Target
  decLE : ∀ a a' : Carrier, Decidable (a ≤ a')
  le_iff_proj : ∀ a a' : Carrier, a ≤ a' ↔ proj a ≤ proj a'

namespace PullbackPreorder

variable {Carrier Target : Type*} [Preorder Target]

instance (o : PullbackPreorder Carrier Target) (a a' : Carrier) :
    @Decidable (@LE.le Carrier o.toLE a a') :=
  o.decLE a a'

/-- Smart constructor: build a `PullbackPreorder` from a projection plus
    decidability of target comparison. The induced `≤` is
    `Preorder.lift`, so `le_iff_proj` is `Iff.rfl`. -/
def ofProj (proj : Carrier → Target)
    (dec : ∀ a a' : Carrier, Decidable (proj a ≤ proj a')) :
    PullbackPreorder Carrier Target where
  __ := Preorder.lift proj
  proj := proj
  decLE := dec
  le_iff_proj _ _ := Iff.rfl

/-- **Change of target (coarsening).**

    Given two `PullbackPreorder`s on the same carrier with projections
    `o1.proj : Carrier → F1` and `o2.proj : Carrier → F2`, plus a
    monotone map `φ : F1 → F2` such that `o2.proj = φ ∘ o1.proj`,
    dominance under `o1` implies dominance under `o2`.

    The converse generally fails: collapsing the target discards
    information. This is the schema behind every "qualitative
    coarsening" bridge — e.g. pointwise-Pareto-on-violations ⇒
    subset-of-satisfied in `Core/Optimization/Pareto.lean`. -/
theorem coarsen_via_monotone {Carrier F1 F2 : Type*}
    [Preorder F1] [Preorder F2]
    (o1 : PullbackPreorder Carrier F1) (o2 : PullbackPreorder Carrier F2)
    (φ : F1 → F2) (hmono : Monotone φ)
    (hcoh : ∀ c : Carrier, o2.proj c = φ (o1.proj c))
    {a a' : Carrier} (h : o1.le a a') : o2.le a a' := by
  rw [o2.le_iff_proj, hcoh, hcoh]
  exact hmono ((o1.le_iff_proj a a').mp h)

end PullbackPreorder

end Core.Order

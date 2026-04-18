import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Feature-Pullback Preorders

A `FeaturePreorder Carrier Feature` is a `Preorder Carrier` realized as the
pullback of a `Preorder Feature` through `feature : Carrier → Feature`. The
induced order is `a ≤ a' ↔ feature a ≤ feature a'`.

This is mathlib's `Preorder.lift` packaged with the witnessing feature
data and decidability of `≤`. It is the common pattern behind several
constructions in linglib:

- `Core.Order.SatisfactionOrdering α Criterion` — feature is the satisfied
  criterion set, feature space is `(Finset Criterion)ᵒᵈ` (or equivalently,
  the violated set with standard ⊆).
- `Core.Constraint.ConstraintSystem.paretoFeaturePreorder` — feature is the
  score vector, feature space is `Profile β n` with pointwise ≤.
- `Semantics.Modality.Kratzer.worldOrdering` — feature is the satisfied
  proposition set, same shape as `SatisfactionOrdering`.

## The reusable theorem

`coarsen_via_monotone` states that a monotone map `φ : F1 → F2` between
feature spaces lifts dominance under the finer feature to dominance under
the coarser feature, provided `f2 = φ ∘ f1`. This is the schema underlying
"Pareto-on-violations ⇒ Pareto-on-satisfaction" and any other forgetful
coarsening between qualitatively-comparable representations.
-/

namespace Core.Order

/-- A preorder on `Carrier` realized as the pullback of a `Preorder Feature`
    through `feature : Carrier → Feature`.

    `extends Preorder Carrier`, so all of mathlib's order vocabulary
    (`≤`, `<`, `Maximal`, `IsMax`) is available; `feature`/`decLE` expose
    the construction data. `le_iff_feature` is the load-bearing coherence
    field — the bundled `≤` agrees with the feature pullback. -/
structure FeaturePreorder (Carrier : Type*) (Feature : Type*) [Preorder Feature]
    extends Preorder Carrier where
  feature : Carrier → Feature
  decLE : ∀ a a' : Carrier, Decidable (a ≤ a')
  le_iff_feature : ∀ a a' : Carrier, a ≤ a' ↔ feature a ≤ feature a'

namespace FeaturePreorder

variable {Carrier Feature : Type*} [Preorder Feature]

instance (o : FeaturePreorder Carrier Feature) (a a' : Carrier) :
    @Decidable (@LE.le Carrier o.toLE a a') :=
  o.decLE a a'

/-- Smart constructor: build a `FeaturePreorder` from a feature map plus
    decidability of feature comparison. The induced `≤` is `Preorder.lift`,
    so `le_iff_feature` is `Iff.rfl`. -/
def ofFeature (feature : Carrier → Feature)
    (dec : ∀ a a' : Carrier, Decidable (feature a ≤ feature a')) :
    FeaturePreorder Carrier Feature where
  __ := Preorder.lift feature
  feature := feature
  decLE := dec
  le_iff_feature _ _ := Iff.rfl

/-- **Change of feature space (coarsening).**

    Given two `FeaturePreorder`s on the same carrier with feature maps
    `o1.feature : Carrier → F1` and `o2.feature : Carrier → F2`, plus a
    monotone map `φ : F1 → F2` such that `o2.feature = φ ∘ o1.feature`,
    dominance under `o1` implies dominance under `o2`.

    The converse generally fails: collapsing the feature space discards
    information. This is the schema behind every "qualitative coarsening"
    bridge — e.g. pointwise-Pareto-on-violations ⇒ subset-of-satisfied
    in `Core/Constraint/Pareto.lean`. -/
theorem coarsen_via_monotone {Carrier F1 F2 : Type*}
    [Preorder F1] [Preorder F2]
    (o1 : FeaturePreorder Carrier F1) (o2 : FeaturePreorder Carrier F2)
    (φ : F1 → F2) (hmono : Monotone φ)
    (hcoh : ∀ c : Carrier, o2.feature c = φ (o1.feature c))
    {a a' : Carrier} (h : o1.le a a') : o2.le a a' := by
  rw [o2.le_iff_feature, hcoh, hcoh]
  exact hmono ((o1.le_iff_feature a a').mp h)

end FeaturePreorder

end Core.Order

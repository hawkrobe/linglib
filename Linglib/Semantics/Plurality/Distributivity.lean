import Linglib.Semantics.Plurality.Basic
import Linglib.Semantics.Plurality.Algebra

/-!
# Tolerant distributivity

This file defines the tolerant distributive operator of [kriz-spector-2021] and the
distributivity-by-maximality classification of [haslinger-etal-2025]. A tolerant distributor
predicates of some nonempty subplurality that the tolerance relation counts as close enough to
the whole; with the identity tolerance it is maximal distribution, and on a singleton every
tolerance agrees.

## Definitions

* `Plurality.Distributivity.distTolerant P tol x w`: some nonempty `z ⪯ x` has every atom
  satisfying `P` at `w`.
* `Plurality.Distributivity.DistMaxClass`: the four cells of obligatory distributivity crossed
  with exception intolerance.

## Main results

* `Plurality.Distributivity.distMaximal_iff_identity`: maximal distribution is tolerant
  distribution under the identity tolerance, on nonempty pluralities.
* `Plurality.Distributivity.distTolerant_singleton`: on a singleton every tolerance reduces to
  the predicate itself.
* `Plurality.Distributivity.distMaximal_iff_star`: maximal distribution is Link's `*` of the
  predicate's atoms, taken as singletons.

## References

* [kriz-spector-2021]
* [haslinger-etal-2025]
* [link-1983]
-/

namespace Plurality.Distributivity

open _root_.Plurality _root_.Plurality.Algebra

variable {Atom W : Type*} {P : Atom → W → Prop} {x : Finset Atom} {w : W}

/-- Tolerant distribution: some nonempty subplurality `z ⪯ x` has every atom satisfying `P` at
`w`. -/
def distTolerant (P : Atom → W → Prop) (tol : Tolerance Atom) (x : Finset Atom) (w : W) : Prop :=
  ∃ z ⊆ x, z.Nonempty ∧ tol.rel z x ∧ ∀ a ∈ z, P a w

instance (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (tol : Tolerance Atom)
    [DecidableRel tol.rel] (x : Finset Atom) (w : W) : Decidable (distTolerant P tol x w) := by
  unfold distTolerant; infer_instance

theorem distMaximal_iff_identity (hne : x.Nonempty) :
    distMaximal P x w ↔ distTolerant P Tolerance.identity x w := by
  refine ⟨λ h => ⟨x, Finset.Subset.refl x, hne, rfl, h⟩, ?_⟩
  rintro ⟨z, -, -, rfl, hz⟩
  exact hz

theorem distTolerant_trivial_of_mem {a : Atom} (ha : a ∈ x) (hPa : P a w) :
    distTolerant P Tolerance.trivial x w :=
  ⟨{a}, Finset.singleton_subset_iff.2 ha, Finset.singleton_nonempty a,
    Finset.singleton_subset_iff.2 ha, λ _ hb => (Finset.mem_singleton.1 hb) ▸ hPa⟩

@[simp]
theorem distMaximal_singleton (a : Atom) : distMaximal P {a} w ↔ P a w := by
  simp [distMaximal]

theorem distMaximal_pair [DecidableEq Atom] (a b : Atom) :
    distMaximal P {a, b} w ↔ P a w ∧ P b w := by
  simp [distMaximal]

/-- On a singleton every tolerance reduces to the predicate itself. -/
theorem distTolerant_singleton (tol : Tolerance Atom) (a : Atom) :
    distTolerant P tol {a} w ↔ P a w := by
  constructor
  · rintro ⟨z, hz, ⟨b, hb⟩, -, hall⟩
    exact (Finset.mem_singleton.1 (hz hb)) ▸ hall b hb
  · intro hPa
    exact ⟨{a}, Finset.Subset.refl _, Finset.singleton_nonempty a, tol.refl _,
      λ _ hb => (Finset.mem_singleton.1 hb) ▸ hPa⟩

/-- Maximal distribution on a nonempty plurality is Link's `*` of the predicate's atoms, taken
as singletons ([link-1983]). -/
theorem distMaximal_iff_star [DecidableEq Atom] (hne : x.Nonempty) :
    distMaximal P x w ↔ star (· ∈ ({·} : Atom → Finset Atom) '' {a | P a w}) x := by
  rw [star_image_singleton, and_iff_right hne]
  exact Iff.rfl

/-- The four cells of [haslinger-etal-2025]: obligatory distributivity crossed with exception
intolerance. -/
inductive DistMaxClass where
  | distMax
  | distNonMax
  | nonDistMax
  | nonDistNonMax
  deriving DecidableEq, Repr

/-- The item applies its predicate to each atom separately. -/
def DistMaxClass.isDistributive : DistMaxClass → Prop
  | .distMax | .distNonMax => True
  | .nonDistMax | .nonDistNonMax => False

instance : DecidablePred DistMaxClass.isDistributive
  | .distMax | .distNonMax => isTrue trivial
  | .nonDistMax | .nonDistNonMax => isFalse not_false

/-- The item tolerates no exceptions. -/
def DistMaxClass.isMaximal : DistMaxClass → Prop
  | .distMax | .nonDistMax => True
  | .distNonMax | .nonDistNonMax => False

instance : DecidablePred DistMaxClass.isMaximal
  | .distMax | .nonDistMax => isTrue trivial
  | .distNonMax | .nonDistNonMax => isFalse not_false

end Plurality.Distributivity

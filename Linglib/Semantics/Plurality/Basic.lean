import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Plural predication over sets of atoms

This file defines the distribution operators shared by the accounts of plural predication in
this directory, over pluralities `x : Finset Atom` and world-indexed predicates
`P : Atom → W → Prop`, together with the tolerance relations of [kriz-spector-2021] that
govern how far a reading may fall short of the whole plurality.

## Definitions

* `Plurality.Tolerance Atom`: a reflexive relation `⪯` on `Finset Atom` contained in `⊆`;
  `y ⪯ x` says `y` is close enough to `x` for current purposes. `Plurality.Tolerance.identity`
  and `Plurality.Tolerance.trivial` are the two extremes.
* `Plurality.distMaximal P x w`: every atom of `x` satisfies `P` at `w`.
* `Plurality.noneSatisfy P x w`: no atom of `x` satisfies `P` at `w`.

## References

* [kriz-spector-2021]
* [haslinger-etal-2025]
-/

namespace Plurality

variable {Atom W : Type*}

/-- A tolerance relation: `y ⪯ x` when the subplurality `y` is close enough to `x` for current
purposes. Reflexive and contained in `⊆`. -/
structure Tolerance (Atom : Type*) where
  /-- `rel y x`: `y` is close enough to `x`. -/
  rel : Finset Atom → Finset Atom → Prop
  refl : ∀ x, rel x x
  subset_of_rel : ∀ {x y}, rel x y → x ⊆ y

namespace Tolerance

/-- Only `x` itself is close enough to `x`. -/
def identity : Tolerance Atom where
  rel x y := x = y
  refl _ := rfl
  subset_of_rel h := h ▸ Finset.Subset.refl _

/-- Every subplurality of `x` is close enough to `x`. -/
def trivial : Tolerance Atom where
  rel x y := x ⊆ y
  refl _ := Finset.Subset.refl _
  subset_of_rel h := h

instance [DecidableEq Atom] : DecidableRel (identity (Atom := Atom)).rel :=
  λ x y => inferInstanceAs (Decidable (x = y))

instance [DecidableEq Atom] : DecidableRel (trivial (Atom := Atom)).rel :=
  λ x y => inferInstanceAs (Decidable (x ⊆ y))

end Tolerance

/-- Maximal distribution: every atom of `x` satisfies `P` at `w`. -/
def distMaximal (P : Atom → W → Prop) (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ x, P a w

instance (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (distMaximal P x w) := by
  unfold distMaximal; infer_instance

/-- No atom of `x` satisfies `P` at `w`. -/
def noneSatisfy (P : Atom → W → Prop) (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ x, ¬ P a w

instance (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (noneSatisfy P x w) := by
  unfold noneSatisfy; infer_instance

end Plurality

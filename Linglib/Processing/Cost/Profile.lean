/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Basic

/-!
# Processing profiles and Pareto comparison

This file defines processing profiles, which record the ordinal difficulty of a linguistic
dependency along four dimensions, namely locality, boundaries crossed, referential load, and
retrieval ease. Profiles are compared by Pareto dominance, the product order of the three cost
dimensions with the dualized ease dimension. A condition counts as harder only when it is at
least as hard on every dimension and strictly harder on one, so two profiles that conflict on
some dimensions are `incomparable` rather than weighed against each other.

## Main definitions

* `ProcessingProfile`: the four ordinal dimensions, with the `PartialOrder` in which `a ≤ b`
  says that `a` is at most as hard as `b`.
* `ProcessingProfile.compare`: the four-way readout of the order (`harder`, `easier`, `equal`,
  `incomparable`).
* `HasProcessingProfile`, `OrderingPrediction`, `verifyOrdering`: the interface studies use to
  state and `decide` ordinal difficulty predictions.

## Main results

* `ProcessingProfile.compare_eq_harder` and its siblings: `compare` answers exactly the order.
* `ProcessingProfile.locality_monotone` and its siblings: increasing a cost dimension cannot make
  processing easier.

## References

* [R. L. Lewis and S. Vasishth, *An Activation-Based Model of Sentence Processing as Skilled
  Memory Retrieval* (2005)][lewis-vasishth-2005]
-/

@[expose] public section

namespace ProcessingModel

/-- A processing profile records the difficulty of a linguistic dependency on four ordinal
    dimensions, where a higher value means more of that factor. Profiles are compared by Pareto
    dominance, without numeric aggregation. -/
structure ProcessingProfile where
  /-- Distance (words/nodes) between filler and integration site -/
  locality : Nat
  /-- Clause or phrase boundaries crossed -/
  boundaries : Nat
  /-- Referential processing load from intervening material
  (0 = none/pronominal, 1 = indefinite, 2 = definite/proper name) -/
  referentialLoad : Nat
  /-- Retrieval facilitation, which richer fillers and higher predictability increase. A higher
  value means easier retrieval, so comparison dualizes this dimension. -/
  ease : Nat
  deriving Repr, DecidableEq

/-- Result of comparing two processing profiles via Pareto dominance. -/
inductive CompareResult where
  /-- Worse-or-equal on all dimensions, strictly worse on at least one. -/
  | harder
  /-- Better-or-equal on all dimensions, strictly better on at least one. -/
  | easier
  /-- Identical on all dimensions. -/
  | equal
  /-- Some dimensions harder, some easier. -/
  | incomparable
  deriving Repr, DecidableEq

namespace ProcessingProfile

/-- `a ≤ b` iff `a` is at most as hard as `b`, that is, at most as high on every cost
    dimension and at least as high on `ease`. -/
instance : LE ProcessingProfile :=
  ⟨fun a b => a.locality ≤ b.locality ∧ a.boundaries ≤ b.boundaries ∧
    a.referentialLoad ≤ b.referentialLoad ∧ b.ease ≤ a.ease⟩

theorem le_def {a b : ProcessingProfile} :
    a ≤ b ↔ a.locality ≤ b.locality ∧ a.boundaries ≤ b.boundaries ∧
      a.referentialLoad ≤ b.referentialLoad ∧ b.ease ≤ a.ease :=
  Iff.rfl

instance : PartialOrder ProcessingProfile where
  le := (· ≤ ·)
  le_refl _ := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  le_trans _ _ _ hab hbc :=
    ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2.1 hbc.2.1,
      Nat.le_trans hab.2.2.1 hbc.2.2.1, Nat.le_trans hbc.2.2.2 hab.2.2.2⟩
  le_antisymm a b hab hba := by
    rw [le_def] at hab hba
    obtain ⟨_, _, _, _⟩ := a
    obtain ⟨_, _, _, _⟩ := b
    simp_all only [mk.injEq]
    omega

instance : DecidableLE ProcessingProfile := fun _ _ =>
  decidable_of_iff _ le_def.symm

instance : DecidableLT ProcessingProfile := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-- `compare a b` reads off how `a` relates to `b` in the Pareto order. -/
def compare (a b : ProcessingProfile) : CompareResult :=
  if a = b then .equal
  else if b < a then .harder
  else if a < b then .easier
  else .incomparable

theorem compare_eq_equal {a b : ProcessingProfile} :
    a.compare b = .equal ↔ a = b := by
  unfold compare
  split_ifs with h₁ h₂ h₃ <;> simp_all

theorem compare_eq_harder {a b : ProcessingProfile} :
    a.compare b = .harder ↔ b < a := by
  unfold compare
  split_ifs with h₁ h₂ h₃ <;> simp_all

theorem compare_eq_easier {a b : ProcessingProfile} :
    a.compare b = .easier ↔ a < b := by
  unfold compare
  split_ifs with h₁ h₂ h₃ <;> simp_all
  exact h₂.asymm

theorem compare_eq_incomparable {a b : ProcessingProfile} :
    a.compare b = .incomparable ↔ ¬ a ≤ b ∧ ¬ b ≤ a := by
  unfold compare
  split_ifs with h₁ h₂ h₃
  · simp_all
  · simp only [false_iff, not_and, not_not]
    exact fun _ => h₂.le
  · simp only [false_iff, not_and]
    exact fun h => absurd h₃.le h
  · simp only [true_iff]
    exact ⟨fun h => h₃ (h.lt_of_ne h₁), fun h => h₂ (h.lt_of_ne (Ne.symm h₁))⟩

/-! ### Monotonicity

Increasing a cost dimension, or decreasing ease, cannot make processing easier. -/

/-- More locality never makes processing easier, as working-memory decay predicts. -/
theorem locality_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with locality := p.locality + k + 1 } |>.compare p) ≠ .easier := by
  rw [Ne, compare_eq_easier]
  exact fun h => absurd h.le (by simp [le_def]; omega)

/-- More boundaries never make processing easier, as interference at retrieval predicts. -/
theorem boundaries_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with boundaries := p.boundaries + k + 1 } |>.compare p) ≠ .easier := by
  rw [Ne, compare_eq_easier]
  exact fun h => absurd h.le (by simp [le_def]; omega)

/-- More referential load never makes processing easier, as similarity-based interference
    predicts. -/
theorem referentialLoad_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with referentialLoad := p.referentialLoad + k + 1 } |>.compare p) ≠ .easier := by
  rw [Ne, compare_eq_easier]
  exact fun h => absurd h.le (by simp [le_def]; omega)

/-- More ease never makes processing harder, since facilitation aids retrieval. -/
theorem ease_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with ease := p.ease + k + 1 } |>.compare p) ≠ .harder := by
  rw [Ne, compare_eq_harder]
  exact fun h => absurd h.le (by simp [le_def]; omega)

end ProcessingProfile

/-- A type has processing profiles when each of its values maps to a `ProcessingProfile`, the
    shared vocabulary that modules use to state processing-based predictions. -/
class HasProcessingProfile (α : Type) where
  profile : α → ProcessingProfile

/-- An ordering prediction says that condition `harder` is harder to process than `easier`. -/
structure OrderingPrediction (α : Type) [HasProcessingProfile α] where
  harder : α
  easier : α
  description : String
  deriving Repr

/-- `verifyOrdering` checks that the Pareto order matches the predicted direction. -/
def verifyOrdering {α : Type} [HasProcessingProfile α]
    (pred : OrderingPrediction α) : Bool :=
  (HasProcessingProfile.profile pred.harder |>.compare
    (HasProcessingProfile.profile pred.easier)) == .harder

end ProcessingModel

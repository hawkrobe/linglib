/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic

/-!
# Processing profiles and Pareto comparison
[lewis-vasishth-2005]

A `ProcessingProfile` records the ordinal difficulty of a linguistic dependency
along four dimensions (locality, boundaries crossed, referential load, retrieval
ease). Profiles are compared by Pareto dominance — the partial order that is the
product of the three cost dimensions with the dualized ease dimension — so a
condition counts as harder only when it is worse-or-equal on every dimension and
strictly worse on one; conflicting dimensions are honestly `incomparable`.
`Core.Optimization.Linearization` characterizes this order: dominance is exactly
agreement of every strictly positive weighted-sum reading, so no magic weights
are chosen here.

## Main definitions

* `ProcessingProfile` — the four ordinal dimensions, with the `PartialOrder`
  instance `a ≤ b` = "`a` at most as hard as `b`".
* `ProcessingProfile.compare` — the four-way readout of the order
  (`harder` / `easier` / `equal` / `incomparable`).
* `HasProcessingProfile`, `OrderingPrediction`, `verifyOrdering` — the interface
  studies use to state and `decide` ordinal difficulty predictions.

## Main results

* `compare_eq_harder` (and siblings) — `compare` answers exactly the order.
* `locality_monotone` (and siblings) — increasing a cost dimension cannot make
  processing easier.
-/

namespace ProcessingModel

/-- A processing profile characterizing the difficulty of a linguistic
    dependency. Each dimension is ordinal (higher = more of that factor);
    comparison is via Pareto dominance — no numeric aggregation. -/
structure ProcessingProfile where
  /-- Distance (words/nodes) between filler and integration site -/
  locality : Nat
  /-- Clause or phrase boundaries crossed -/
  boundaries : Nat
  /-- Referential processing load from intervening material
  (0 = none/pronominal, 1 = indefinite, 2 = definite/proper name) -/
  referentialLoad : Nat
  /-- Retrieval facilitation: richer fillers, higher predictability
  (higher = easier retrieval, so this dimension is dualized in comparison) -/
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

/-- Pareto order: `a ≤ b` iff `a` is at most as hard as `b` — at most as high
    on every cost dimension and at least as high on `ease`. -/
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

/-- The four-way readout of the Pareto order. -/
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

Increasing a cost dimension (or decreasing ease) cannot make processing easier
— one-line consequences of the order. -/

/-- More locality → not easier (working memory decay). -/
theorem locality_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with locality := p.locality + k + 1 } |>.compare p) ≠ .easier := by
  rw [Ne, compare_eq_easier]
  exact fun h => absurd h.le (by simp [le_def]; omega)

/-- More boundaries → not easier (interference at retrieval). -/
theorem boundaries_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with boundaries := p.boundaries + k + 1 } |>.compare p) ≠ .easier := by
  rw [Ne, compare_eq_easier]
  exact fun h => absurd h.le (by simp [le_def]; omega)

/-- More referential load → not easier (similarity-based interference). -/
theorem referentialLoad_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with referentialLoad := p.referentialLoad + k + 1 } |>.compare p) ≠ .easier := by
  rw [Ne, compare_eq_easier]
  exact fun h => absurd h.le (by simp [le_def]; omega)

/-- More ease → not harder (facilitation aids retrieval). -/
theorem ease_monotone (p : ProcessingProfile) (k : Nat) :
    ({ p with ease := p.ease + k + 1 } |>.compare p) ≠ .harder := by
  rw [Ne, compare_eq_harder]
  exact fun h => absurd h.le (by simp [le_def]; omega)

end ProcessingProfile

/-- Typeclass for types that can be mapped to processing profiles: the shared
    vocabulary modules use to state processing-based predictions. -/
class HasProcessingProfile (α : Type) where
  profile : α → ProcessingProfile

/-- An ordering prediction: condition `harder` should be harder than `easier`. -/
structure OrderingPrediction (α : Type) [HasProcessingProfile α] where
  harder : α
  easier : α
  description : String
  deriving Repr

/-- Verify that Pareto ordering matches the predicted direction. -/
def verifyOrdering {α : Type} [HasProcessingProfile α]
    (pred : OrderingPrediction α) : Bool :=
  (HasProcessingProfile.profile pred.harder |>.compare
    (HasProcessingProfile.profile pred.easier)) == .harder

end ProcessingModel

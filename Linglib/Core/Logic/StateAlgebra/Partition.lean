import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Union

/-!
# State partition primitives — pure `Finset` combinatorics

The combinatorial primitives underlying split disjunction in team-semantic
logics (BSML, QBSML, dependence logic, Yang-Väänänen propositional team logic).
This file is **theory-neutral**: nothing in it knows about evaluation,
support, or formulas. It provides only the partition relations.

## What this gives consumers

A team-semantic logic interprets `φ ∨ ψ` as: the state can be split into two
substates, each supporting one disjunct. This file factors the *partition
condition itself* away from any particular notion of "support". Consumers
(BSML, QBSML, ...) plug in their own per-formula evaluation predicates;
this file owns the structural claim that such a split exists.

The two variants — vanilla `splitsAs` and non-empty `splitsAsNE` — correspond
to plain split disjunction and Aloni's pragmatically-enriched version
(`[φ ∨ ψ]⁺ = ([φ]⁺ ∨ [ψ]⁺) ∧ NE`, where the NE conjunct propagates to the
substates and forces them non-empty).

## Naming

We use `splitsAs` rather than `partition` because mathlib reserves
`Finset.partition` for equivalence-class partitions (whose parts are pairwise
disjoint and exhaustive). Team-semantic split disjunction does not require
disjointness — `t₁ ∩ t₂` may be non-empty.
-/

namespace Core.Logic.StateAlgebra

variable {α : Type*}

/-- Binary cover: `s` is the union of `t₁` and `t₂`. The two substates may
    overlap; only their union must equal `s`. This is the structural
    condition under team-semantic split disjunction (Aloni 2022 Definition 2;
    Yang & Väänänen 2017).

    The arguments are ordered `s t₁ t₂` so `splitsAs s` reads as a relation
    "splits the state s into ...". -/
def splitsAs (s t₁ t₂ : Finset α) : Prop :=
  t₁ ∪ t₂ = s

/-- Binary cover with both parts non-empty. Used by pragmatically-enriched
    split disjunction in BSML+ / QBSML+ (Aloni 2022 §3.3): `[φ ∨ ψ]⁺` requires
    both substates to be non-empty (forced by the NE conjunct propagating
    through enrichment). -/
def splitsAsNE (s t₁ t₂ : Finset α) : Prop :=
  t₁ ∪ t₂ = s ∧ t₁.Nonempty ∧ t₂.Nonempty

@[simp] theorem splitsAs_iff (s t₁ t₂ : Finset α) :
    splitsAs s t₁ t₂ ↔ t₁ ∪ t₂ = s := Iff.rfl

@[simp] theorem splitsAsNE_iff (s t₁ t₂ : Finset α) :
    splitsAsNE s t₁ t₂ ↔ t₁ ∪ t₂ = s ∧ t₁.Nonempty ∧ t₂.Nonempty := Iff.rfl

theorem splitsAsNE_imp_splitsAs (s t₁ t₂ : Finset α)
    (h : splitsAsNE s t₁ t₂) : splitsAs s t₁ t₂ := h.1

/-- The trivial split: `s = s ∪ ∅`. Used by classical formulas, which are
    supported on the empty state vacuously, allowing degenerate splits. -/
theorem splitsAs_self_empty (s : Finset α) : splitsAs s s ∅ := by
  simp [splitsAs]

theorem splitsAs_empty_self (s : Finset α) : splitsAs s ∅ s := by
  simp [splitsAs]

/-- The reflexive split: `s = s ∪ s` (parts may overlap). -/
theorem splitsAs_self_self (s : Finset α) : splitsAs s s s := by
  simp [splitsAs]

theorem splitsAs_symm {s t₁ t₂ : Finset α}
    (h : splitsAs s t₁ t₂) : splitsAs s t₂ t₁ := by
  rw [splitsAs] at h ⊢; rw [Finset.union_comm]; exact h

theorem splitsAsNE_symm {s t₁ t₂ : Finset α}
    (h : splitsAsNE s t₁ t₂) : splitsAsNE s t₂ t₁ :=
  ⟨splitsAs_symm h.1, h.2.2, h.2.1⟩

/-- Substate property: if `splitsAs s t₁ t₂`, then `t₁ ⊆ s`. -/
theorem splitsAs_left_subset {s t₁ t₂ : Finset α}
    (h : splitsAs s t₁ t₂) : t₁ ⊆ s := by
  rw [splitsAs] at h; exact h ▸ Finset.subset_union_left

theorem splitsAs_right_subset {s t₁ t₂ : Finset α}
    (h : splitsAs s t₁ t₂) : t₂ ⊆ s := by
  rw [splitsAs] at h; exact h ▸ Finset.subset_union_right

instance (s t₁ t₂ : Finset α) [DecidableEq α] : Decidable (splitsAs s t₁ t₂) := by
  unfold splitsAs; infer_instance

instance (s t₁ t₂ : Finset α) [DecidableEq α] : Decidable (splitsAsNE s t₁ t₂) := by
  unfold splitsAsNE; infer_instance

end Core.Logic.StateAlgebra

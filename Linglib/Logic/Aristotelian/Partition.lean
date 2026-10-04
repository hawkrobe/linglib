module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Partition.Finpartition

/-!
# The partition induced by a fragment

A fragment of a Boolean algebra `α` is a finite family `φ : ι → α`. The anchor of a polarity
assignment `σ : ι → Bool` is the meet of the `φ i` with `σ i` true and of the complements of the
others. Distinct anchors are disjoint and the anchors join to `⊤`, so the nonzero anchors are the
parts of a partition of `⊤`, the partition induced by `φ`. Demey and Smessaert build the bitstring
semantics of a fragment on this partition.

## Main definitions

* `Aristotelian.anchor`: the anchor of a polarity assignment.
* `Aristotelian.partition`: the partition induced by a fragment.

## Main results

* `Aristotelian.disjoint_anchor`, `Aristotelian.sup_anchor`: the anchors are mutually exclusive
  and jointly exhaustive.
* `Aristotelian.partition_sumElim`: the partition induced by the union of two fragments is the
  meet of their partitions.

## Implementation notes

Demey and Smessaert take the formulas of a logical system up to equivalence, its
Lindenbaum–Tarski algebra; any Boolean algebra serves. A fragment is an indexed family, so the
union of two fragments is `Sum.elim`. Their meet of partitions is the meet of `Finpartition`, and
refinement is its order. `Finpartition.atomise` is the same construction for a family of finsets.

## References

* [demey-smessaert-2018]
-/

@[expose] public section

namespace Aristotelian

open Finset

variable {α ι κ : Type*} [BooleanAlgebra α] [Fintype ι] [Fintype κ]

/-- The anchor of a polarity assignment `σ` is the meet of the `φ i` with `σ i` true and of the
complements of the others ([demey-smessaert-2018] Definition 5). -/
def anchor (φ : ι → α) (σ : ι → Bool) : α :=
  univ.inf fun i ↦ if σ i then φ i else (φ i)ᶜ

variable {φ : ι → α} {σ τ : ι → Bool} {i : ι}

theorem anchor_le_of_true (h : σ i = true) : anchor φ σ ≤ φ i :=
  (inf_le (f := fun i ↦ if σ i then φ i else (φ i)ᶜ) (mem_univ i)).trans_eq (by simp [h])

theorem anchor_le_compl_of_false (h : σ i = false) : anchor φ σ ≤ (φ i)ᶜ :=
  (inf_le (f := fun i ↦ if σ i then φ i else (φ i)ᶜ) (mem_univ i)).trans_eq (by simp [h])

/-- Anchors of distinct polarity assignments are disjoint ([demey-smessaert-2018] Lemma 3). -/
theorem disjoint_anchor (h : σ ≠ τ) : Disjoint (anchor φ σ) (anchor φ τ) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  cases hσ : σ i
  · have hτ : τ i = true := by simpa [hσ] using hi.symm
    exact (disjoint_compl_left.mono_left (anchor_le_compl_of_false hσ)).mono_right
      (anchor_le_of_true hτ)
  · have hτ : τ i = false := by simpa [hσ] using hi.symm
    exact (disjoint_compl_right.mono_left (anchor_le_of_true hσ)).mono_right
      (anchor_le_compl_of_false hτ)

theorem anchor_sumElim (φ : ι → α) (ψ : κ → α) (σ : ι ⊕ κ → Bool) :
    anchor (Sum.elim φ ψ) σ = anchor φ (σ ∘ .inl) ⊓ anchor ψ (σ ∘ .inr) := by
  simp only [anchor, ← univ_disjSum_univ, inf_disjSum]
  rfl

variable [DecidableEq ι]

variable (φ) in
/-- The anchors join to `⊤` ([demey-smessaert-2018] Lemma 3). -/
theorem sup_anchor : univ.sup (anchor φ) = ⊤ := by
  suffices ∀ s : Finset ι,
      univ.sup (fun σ : ι → Bool ↦ s.inf fun i ↦ if σ i then φ i else (φ i)ᶜ) = ⊤ from this univ
  intro s
  induction s using Finset.induction with
  | empty => simp [sup_const univ_nonempty]
  | insert j s hj ih =>
    refine eq_top_iff.2 (ih.symm.trans_le (Finset.sup_le fun σ _ ↦ ?_))
    set g : (ι → Bool) → α := fun τ ↦ s.inf fun i ↦ if τ i then φ i else (φ i)ᶜ
    have hg (b : Bool) : g (Function.update σ j b) = g σ :=
      Finset.inf_congr rfl fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
    calc g σ = (φ j ⊓ g σ) ⊔ ((φ j)ᶜ ⊓ g σ) := by rw [← inf_sup_right, sup_compl_eq_top, top_inf_eq]
      _ ≤ _ := by
        refine sup_le (le_sup_of_le (mem_univ (Function.update σ j true)) (le_of_eq ?_))
          (le_sup_of_le (mem_univ (Function.update σ j false)) (le_of_eq ?_))
        · rw [Finset.inf_insert, Function.update_self, ← hg true]; rfl
        · rw [Finset.inf_insert, Function.update_self, ← hg false]; rfl

variable [DecidableEq α]

variable (φ) in
/-- The partition induced by `φ` has the nonzero anchors as parts ([demey-smessaert-2018]
Definition 5). -/
def partition : Finpartition (⊤ : α) :=
  .ofErase (univ.image (anchor φ))
    (Set.PairwiseDisjoint.supIndep fun a ha b hb hab ↦ by
      obtain ⟨σ, -, rfl⟩ := mem_image.1 ha
      obtain ⟨τ, -, rfl⟩ := mem_image.1 hb
      exact disjoint_anchor fun h ↦ hab (h ▸ rfl))
    (by rw [sup_image, Function.id_comp, sup_anchor])

theorem mem_partition_parts {a : α} : a ∈ (partition φ).parts ↔ a ≠ ⊥ ∧ ∃ σ, anchor φ σ = a := by
  simp [partition]

variable [DecidableEq κ]

/-- The partition induced by the union of two fragments is the meet of the partitions they
induce ([demey-smessaert-2018] Lemma 4). -/
theorem partition_sumElim (φ : ι → α) (ψ : κ → α) :
    partition (Sum.elim φ ψ) = partition φ ⊓ partition ψ := by
  ext a
  simp only [Finpartition.parts_inf, mem_erase, mem_image, mem_product, mem_partition_parts,
    Prod.exists, anchor_sumElim]
  refine and_congr_right fun ha ↦ ⟨?_, ?_⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨_, _, ⟨⟨ne_bot_of_le_ne_bot ha inf_le_left, _, rfl⟩,
      ne_bot_of_le_ne_bot ha inf_le_right, _, rfl⟩, rfl⟩
  · rintro ⟨-, -, ⟨⟨-, σ, rfl⟩, -, τ, rfl⟩, rfl⟩
    exact ⟨Sum.elim σ τ, by simp [Function.comp_def]⟩

end Aristotelian

import Linglib.Core.Logic.Aristotelian.Basic
import Linglib.Core.Logic.Aristotelian.Partition
import Mathlib.Data.Fintype.Order
import Mathlib.Order.BooleanSubalgebra

/-!
# Bitstring semantics for logical fragments

Per [demey-smessaert-2018] §3.2. For a fragment `φ : ι → W → Bool`, the
bitstring of a formula `ψ` in the Boolean closure of `Set.range φ` records, for
each consistent anchor cell, whether that cell entails `ψ`. This map is a Boolean
isomorphism onto `Fin n → Bool` (Theorem 1), hence an Aristotelian isomorphism
(Theorem 2).

## Main declarations

* `bitstringOf` — the bitstring map (Definition 7).
* `bitstringOrderIso` — the isomorphism `closure (Set.range φ) ≃o (Fin n → Bool)`.
* `isAtom_anchor` — consistent anchor cells are the atoms of the closure.
* `isContradictory_bitstring_iff` and siblings — the Aristotelian relations transfer.

## Implementation notes

The closure-membership lemmas need only `[Fintype ι]` (literal membership needs no
index instances). `[DecidableEq ι]` enters only with the `partition`, so the
world-enumeration declarations — which also require `[Fintype W]` — live in
`section WorldEnumeration` below.

`isAtom_anchor` is the `partition`-cell case of mathlib's atom representation for
finite Boolean algebras (`CompleteAtomicBooleanAlgebra.toSetOfIsAtom`); the
bitstring isomorphism is its explicit `Fin n`-indexed form.
-/

namespace Aristotelian

/-- A `Bool`-valued infimum is `true` iff every entry is. -/
private theorem iInf_bool_eq_true {κ : Type*} (g : κ → Bool) :
    (⨅ i, g i) = true ↔ ∀ i, g i = true := by
  rw [← top_eq_true, iInf_eq_top]

variable {W : Type*} {ι : Type*}

/-! ### Anchor-decidedness -/

section
variable [Fintype ι] (φ : ι → W → Bool)

/-- Lemma 6 for the indexed-family `anchor`: every closure element is entailed by
an anchor or by its complement ([demey-smessaert-2018]). -/
theorem anchor_le_or_le_compl_mem_closure (σ : ι → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) :
    anchor φ σ ≤ ψ ∨ anchor φ σ ≤ ψᶜ := by
  induction hψ using BooleanSubalgebra.closure_bot_sup_induction with
  | mem ψ' hψ' =>
    obtain ⟨i, rfl⟩ := hψ'
    by_cases h : σ i = true
    · left
      rw [le_iff_forall]
      intro w hw
      simp only [anchor, decide_eq_true_eq] at hw
      simpa only [if_pos h] using hw i
    · right
      rw [le_iff_forall]
      intro w hw
      simp only [anchor, decide_eq_true_eq] at hw
      have := hw i
      rw [if_neg h] at this
      simp only [Pi.compl_apply, this, Bool.compl_eq_bnot, Bool.not_false]
  | bot => exact Or.inr (by simp only [compl_bot, le_top])
  | sup x _ y _ ihx ihy =>
    rcases ihx with hx | hx
    · left; exact hx.trans le_sup_left
    rcases ihy with hy | hy
    · left; exact hy.trans le_sup_right
    · right; rw [compl_sup]; exact le_inf hx hy
  | compl x _ ih =>
    rcases ih with h | h
    · right; rw [compl_compl]; exact h
    · left; exact h

/-! ### Anchor formulas lie in the closure -/

omit [Fintype ι] in
private theorem lit_mem_closure (σ : ι → Bool) (i : ι) :
    (if σ i then φ i else (φ i)ᶜ) ∈
    BooleanSubalgebra.closure (Set.range φ) := by
  cases h : σ i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact BooleanSubalgebra.compl_mem (BooleanSubalgebra.subset_closure ⟨i, rfl⟩)
  · simp only [↓reduceIte]
    exact BooleanSubalgebra.subset_closure ⟨i, rfl⟩

/-- An anchor is the infimum of its literals `±φ i`. -/
theorem anchor_eq_iInf (σ : ι → Bool) :
    anchor φ σ = ⨅ i, (if σ i then φ i else (φ i)ᶜ) := by
  funext w
  rw [iInf_apply]
  unfold anchor
  rw [Bool.eq_iff_iff, decide_eq_true_eq, iInf_bool_eq_true]
  refine forall_congr' fun i => ?_
  rw [ite_apply]
  cases hi : σ i
  · simp only [Bool.false_eq_true, ↓reduceIte, Pi.compl_apply, Bool.compl_eq_bnot,
      Bool.not_eq_eq_eq_not, Bool.not_true]
  · simp only [↓reduceIte]

/-- Anchor formulas lie in the Boolean closure of `Set.range φ` — an anchor is the
infimum of its literals, each of which lies in the closure. -/
theorem anchor_mem_closure (σ : ι → Bool) :
    anchor φ σ ∈ BooleanSubalgebra.closure (Set.range φ) := by
  rw [anchor_eq_iInf]
  exact BooleanSubalgebra.iInf_mem (fun i => lit_mem_closure φ σ i)

/-! ### Atoms of the closure -/

/-- A consistent anchor cell is an atom of `closure (Set.range φ)`: it is below or
disjoint from every closure element (Lemma 6), so once nonzero nothing lies
strictly between it and `⊥`. -/
theorem isAtom_anchor (σ : ι → Bool) (hCons : ∃ w, anchor φ σ w = true) :
    IsAtom (⟨anchor φ σ, anchor_mem_closure φ σ⟩ :
      BooleanSubalgebra.closure (Set.range φ)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · intro hbot
    obtain ⟨w, hw⟩ := hCons
    have hval : anchor φ σ = (⊥ : W → Bool) := congrArg Subtype.val hbot
    rw [hval] at hw
    exact Bool.noConfusion hw
  · have hble : (b : W → Bool) ≤ anchor φ σ := hb.le
    rcases anchor_le_or_le_compl_mem_closure φ σ b.2 with hL | hR
    · exact absurd (Subtype.ext (le_antisymm hble hL)) hb.ne
    · have hself : (b : W → Bool) ≤ (b : W → Bool)ᶜ := hble.trans hR
      exact Subtype.ext (le_compl_self.mp hself)

/-- Converse of `isAtom_anchor`: every atom of `closure (Set.range φ)` is a consistent
anchor cell. -/
theorem atom_imp_anchor {a : BooleanSubalgebra.closure (Set.range φ)} (ha : IsAtom a) :
    ∃ σ, a.val = anchor φ σ ∧ ∃ w, anchor φ σ w = true := by
  obtain ⟨w, hw⟩ : ∃ w, a.val w = true := by
    by_contra hcon
    push Not at hcon
    refine ha.1 (Subtype.ext (funext fun w => ?_))
    show a.val w = (⊥ : W → Bool) w
    simp only [Pi.bot_apply]
    exact Bool.eq_false_iff.mpr (hcon w)
  obtain ⟨σ, hcons⟩ := anchor_jointly_exhaustive φ w
  refine ⟨σ, ?_, w, hcons⟩
  have hα : IsAtom (⟨anchor φ σ, anchor_mem_closure φ σ⟩ :
      BooleanSubalgebra.closure (Set.range φ)) := isAtom_anchor φ σ ⟨w, hcons⟩
  rcases anchor_le_or_le_compl_mem_closure φ σ a.2 with hL | hR
  · exact (congrArg Subtype.val ((ha.le_iff_eq hα.ne_bot).mp hL)).symm
  · have hcompl : (a.val)ᶜ w = true := (le_iff_forall.mp hR) w hcons
    simp only [Pi.compl_apply, hw] at hcompl
    exact absurd hcompl (by decide)

/-- The atoms of `closure (Set.range φ)` are **exactly** the consistent anchor cells — the
partition-cell ↔ atom correspondence underlying the bitstring representation. -/
theorem isAtom_iff_anchor {a : BooleanSubalgebra.closure (Set.range φ)} :
    IsAtom a ↔ ∃ σ, a.val = anchor φ σ ∧ ∃ w, anchor φ σ w = true := by
  refine ⟨atom_imp_anchor φ, ?_⟩
  rintro ⟨σ, heq, hcons⟩
  rw [show a = ⟨anchor φ σ, anchor_mem_closure φ σ⟩ from Subtype.ext heq]
  exact isAtom_anchor φ σ hcons

end

section WorldEnumeration

variable [Fintype W] [Fintype ι] [DecidableEq ι] (φ : ι → W → Bool)

/-! ### Bitstring representation (Definition 7) -/

/-- A positional index for the anchor cells, via `partition.equivFin`. -/
noncomputable def anchorIndex :
    Fin (partition ι W φ).card → (ι → Bool) :=
  fun i => ((partition ι W φ).equivFin.symm i).val

/-- The bitstring of `ψ` relative to `φ`: bit `i` is `true` iff anchor `i` entails
`ψ` ([demey-smessaert-2018], Definition 7). -/
noncomputable def bitstringOf (ψ : W → Bool) :
    Fin (partition ι W φ).card → Bool :=
  fun i => decide (∀ w, anchor φ (anchorIndex φ i) w = true → ψ w = true)

/-- Each partition cell is consistent: some world satisfies the anchor at index `i`. -/
theorem anchorIndex_consistent (i : Fin (partition ι W φ).card) :
    ∃ w, anchor φ (anchorIndex φ i) w = true := by
  have hMem := ((partition ι W φ).equivFin.symm i).property
  simp only [partition, Finset.mem_filter] at hMem
  exact of_decide_eq_true hMem.2

/-! ### Bitstring evaluation -/

/-- If `w` satisfies anchor `i` and `ψ` is in the closure, then `bitstringOf φ ψ i`
is `ψ w`. -/
theorem bitstringOf_apply_at_anchor {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ))
    (i : Fin (partition ι W φ).card) {w : W}
    (hw : anchor φ (anchorIndex φ i) w = true) :
    bitstringOf φ ψ i = ψ w := by
  rcases anchor_le_or_le_compl_mem_closure φ (anchorIndex φ i) hψ with hL | hR
  · have hβ : bitstringOf φ ψ i = true := by
      simp only [bitstringOf, decide_eq_true_eq]
      exact fun w' hw' => (le_iff_forall.mp hL) w' hw'
    have hψw : ψ w = true := (le_iff_forall.mp hL) w hw
    rw [hβ, hψw]
  · have hψw : ψ w = false := by
      have := (le_iff_forall.mp hR) w hw
      simpa only [Pi.compl_apply, Bool.compl_eq_bnot, Bool.not_eq_eq_eq_not,
        Bool.not_true] using this
    have hβ : bitstringOf φ ψ i = false := by
      cases hb : bitstringOf φ ψ i
      · rfl
      · exfalso
        simp only [bitstringOf, decide_eq_true_eq] at hb
        rw [hb w hw] at hψw
        exact absurd hψw (by decide)
    rw [hβ, hψw]

/-- An anchor index satisfied by `w`. -/
noncomputable def worldAnchorIndex (w : W) : Fin (partition ι W φ).card :=
  let σ := Classical.choose (anchor_jointly_exhaustive φ w)
  let hσ := Classical.choose_spec (anchor_jointly_exhaustive φ w)
  (partition ι W φ).equivFin ⟨σ, by
    simp only [partition, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, decide_eq_true ⟨w, hσ⟩⟩⟩

theorem anchor_worldAnchorIndex (w : W) :
    anchor φ (anchorIndex φ (worldAnchorIndex φ w)) w = true := by
  unfold worldAnchorIndex anchorIndex
  simp only [Equiv.symm_apply_apply]
  exact Classical.choose_spec (anchor_jointly_exhaustive φ w)

/-- `bitstringOf φ ψ` at a world's anchor index recovers `ψ` at that world. -/
theorem bitstringOf_apply_at_world {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) (w : W) :
    bitstringOf φ ψ (worldAnchorIndex φ w) = ψ w :=
  bitstringOf_apply_at_anchor φ hψ _ (anchor_worldAnchorIndex φ w)

/-- `bitstringOf φ` is injective on the Boolean closure. -/
theorem bitstringOf_injOn_closure :
    Set.InjOn (bitstringOf φ)
      (BooleanSubalgebra.closure (Set.range φ) : Set (W → Bool)) := by
  intro ψ₁ hψ₁ ψ₂ hψ₂ hEq
  funext w
  rw [← bitstringOf_apply_at_world φ hψ₁ w, hEq, bitstringOf_apply_at_world φ hψ₂ w]

/-! ### The inverse and round trips -/

/-- The supremum of the anchor cells whose bit is `true` — the inverse of
`bitstringOf` on the closure. -/
noncomputable def bitstringInverse (b : Fin (partition ι W φ).card → Bool) : W → Bool :=
  ⨆ i, (if b i then anchor φ (anchorIndex φ i) else (⊥ : W → Bool))

theorem bitstringInverse_mem_closure (b : Fin (partition ι W φ).card → Bool) :
    bitstringInverse φ b ∈ BooleanSubalgebra.closure (Set.range φ) := by
  unfold bitstringInverse
  apply BooleanSubalgebra.iSup_mem
  intro i
  cases h : b i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (BooleanSubalgebra.closure (Set.range φ)).bot_mem
  · simp only [↓reduceIte]
    exact anchor_mem_closure φ _

private theorem anchorIndex_injective :
    Function.Injective (anchorIndex φ) := by
  intro i j h
  unfold anchorIndex at h
  exact (partition ι W φ).equivFin.symm.injective (Subtype.ext h)

private theorem anchor_at_world_unique {i j : Fin (partition ι W φ).card} {w : W}
    (hi : anchor φ (anchorIndex φ i) w = true)
    (hj : anchor φ (anchorIndex φ j) w = true) :
    i = j := by
  by_contra hne
  apply anchor_mutually_exclusive φ (anchorIndex φ i) (anchorIndex φ j)
    (fun heq => hne (anchorIndex_injective φ heq)) w
  exact ⟨hi, hj⟩

/-- If `w` satisfies anchor `j`, then `bitstringInverse φ b w` is the `j`-th bit:
the `iSup` collapses to the summand at `j`. -/
theorem bitstringInverse_apply_at_anchor (b : Fin (partition ι W φ).card → Bool)
    (j : Fin (partition ι W φ).card) {w : W}
    (hw : anchor φ (anchorIndex φ j) w = true) :
    bitstringInverse φ b w = b j := by
  unfold bitstringInverse
  rw [iSup_apply]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    by_cases hij : i = j
    · subst hij
      cases hbi : b i <;>
        simp only [hw, Bool.false_eq_true, ↓reduceIte, Pi.bot_apply, bot_le, le_refl]
    · have hf : anchor φ (anchorIndex φ i) w = false := by
        cases hai : anchor φ (anchorIndex φ i) w
        · rfl
        · exact absurd (anchor_at_world_unique φ hai hw) hij
      cases hbi : b i <;>
        simp only [hf, Bool.false_eq_true, ↓reduceIte, Pi.bot_apply, bot_le, Bool.false_le]
  · refine le_iSup_of_le j ?_
    cases hbj : b j
    · exact Bool.false_le _
    · simp only [↓reduceIte, hw, le_refl]

theorem bitstringOf_bitstringInverse (b : Fin (partition ι W φ).card → Bool) :
    bitstringOf φ (bitstringInverse φ b) = b := by
  funext j
  obtain ⟨w, hw⟩ := anchorIndex_consistent φ j
  rw [bitstringOf_apply_at_anchor φ (bitstringInverse_mem_closure φ b) j hw]
  exact bitstringInverse_apply_at_anchor φ b j hw

theorem bitstringInverse_bitstringOf {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) :
    bitstringInverse φ (bitstringOf φ ψ) = ψ := by
  funext w
  rw [bitstringInverse_apply_at_anchor φ (bitstringOf φ ψ)
      (worldAnchorIndex φ w) (anchor_worldAnchorIndex φ w)]
  exact bitstringOf_apply_at_world φ hψ w

/-! ### Theorem 1: the Boolean isomorphism -/

/-- **Theorem 1** ([demey-smessaert-2018]): `bitstringOf φ` is an order
isomorphism `closure (Set.range φ) ≃o (Fin n → Bool)`, `n = |partition|`. -/
noncomputable def bitstringOrderIso :
    BooleanSubalgebra.closure (Set.range φ) ≃o
    (Fin (partition ι W φ).card → Bool) where
  toFun := fun ⟨ψ, _⟩ => bitstringOf φ ψ
  invFun := fun b => ⟨bitstringInverse φ b, bitstringInverse_mem_closure φ b⟩
  left_inv := fun ⟨ψ, hψ⟩ => Subtype.ext (bitstringInverse_bitstringOf φ hψ)
  right_inv := fun b => bitstringOf_bitstringInverse φ b
  map_rel_iff' := by
    rintro ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    show bitstringOf φ ψ₁ ≤ bitstringOf φ ψ₂ ↔ ψ₁ ≤ ψ₂
    rw [le_iff_forall, le_iff_forall]
    constructor
    · intro h w hw₁
      have := h (worldAnchorIndex φ w)
      rw [bitstringOf_apply_at_world φ hψ₁ w,
          bitstringOf_apply_at_world φ hψ₂ w] at this
      exact this hw₁
    · intro h i
      obtain ⟨w, hw⟩ := anchorIndex_consistent φ i
      rw [bitstringOf_apply_at_anchor φ hψ₁ i hw,
          bitstringOf_apply_at_anchor φ hψ₂ i hw]
      exact h w

/-! ### Theorem 2: Aristotelian transfer

Each relation transfers along the Boolean isomorphism `bitstringOrderIso`
([demey-smessaert-2018], Theorem 2). -/

section Transfer
variable (a b : BooleanSubalgebra.closure (Set.range φ))

theorem isContradictory_bitstring_iff :
    IsContradictory (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsContradictory a b :=
  isContradictory_apply_orderIso (bitstringOrderIso φ)

theorem isContrary_bitstring_iff :
    IsContrary (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsContrary a b :=
  isContrary_apply_orderIso (bitstringOrderIso φ)

theorem isSubcontrary_bitstring_iff :
    IsSubcontrary (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsSubcontrary a b :=
  isSubcontrary_apply_orderIso (bitstringOrderIso φ)

theorem isSubaltern_bitstring_iff :
    IsSubaltern (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsSubaltern a b :=
  isSubaltern_apply_orderIso (bitstringOrderIso φ)

end Transfer

end WorldEnumeration

end Aristotelian

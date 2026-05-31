import Linglib.Core.Logic.Aristotelian.Basic
import Linglib.Core.Logic.Aristotelian.Partition
import Linglib.Core.Logic.Aristotelian.Atoms
import Mathlib.Data.Fintype.Order
import Mathlib.Order.BooleanSubalgebra

/-!
# Bitstring semantics for logical fragments

Per @cite{demey-smessaert-2018} §3.2. For a fragment `φ : ι → W → Bool`, the
bitstring of a formula `ψ` in the Boolean closure of `Set.range φ` records, for
each consistent anchor cell, whether that cell entails `ψ`. This map is a Boolean
isomorphism onto `Fin n → Bool` (Theorem 1), hence an Aristotelian isomorphism
(Theorem 2).

## Main declarations

* `bitstringOf` — the bitstring map (Definition 7).
* `bitstringOf_orderIso` — the isomorphism `closure (Set.range φ) ≃o (Fin n → Bool)`.
* `isAtom_anchor` — consistent anchor cells are the atoms of the closure.
* `isContradictory_bitstring_iff` and siblings — the Aristotelian relations transfer.

## Implementation notes

The closure-membership lemmas need only `[Fintype ι]` and live in the plain `{W}`
scope; the world-enumeration declarations index the `partition` and live in
`section WorldEnumeration` (`[Fintype W]`) below.
-/

namespace Aristotelian

variable {W : Type*}

/-! ### Anchor-decidedness -/

/-- Lemma 6 for the indexed-family `anchor`: every closure element is entailed by
an anchor or by its complement (@cite{demey-smessaert-2018}). The BA-generic form
is `Atoms.lean::anchorBA_le_or_le_compl_mem_closure`. -/
theorem anchor_le_or_le_compl_mem_closure
    {ι : Type*} [Fintype ι] (φ : ι → W → Bool) (σ : ι → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) :
    anchor φ σ ≤ ψ ∨ anchor φ σ ≤ ψᶜ := by
  induction hψ using BooleanSubalgebra.closure_bot_sup_induction with
  | mem ψ' hψ' =>
    obtain ⟨i, rfl⟩ := hψ'
    by_cases h : σ i = true
    · left
      rw [le_iff_forall]
      intro w hw
      unfold anchor at hw
      rw [decide_eq_true_eq] at hw
      have := hw i
      rw [if_pos h] at this
      exact this
    · right
      rw [le_iff_forall]
      intro w hw
      have hf : σ i = false := Bool.eq_false_iff.mpr h
      unfold anchor at hw
      rw [decide_eq_true_eq] at hw
      have := hw i
      rw [if_neg h] at this
      simp [this]
  | bot =>
    right
    rw [le_iff_forall]
    intro w _
    rfl
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

private theorem lit_mem_closure {ι : Type*} [Fintype ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (i : ι) :
    (if σ i then φ i else (φ i)ᶜ) ∈
    BooleanSubalgebra.closure (Set.range φ) := by
  by_cases h : σ i = true
  · simp only [h, ↓reduceIte]
    exact BooleanSubalgebra.subset_closure ⟨i, rfl⟩
  · have hf : σ i = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact BooleanSubalgebra.compl_mem (BooleanSubalgebra.subset_closure ⟨i, rfl⟩)

/-- The anchor over a `Finset s`: the conjunction of literals `±φ i` for `i ∈ s`. -/
private def anchorOnFinset {ι : Type*} [DecidableEq ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (s : Finset ι) : W → Bool :=
  fun w => decide (∀ i ∈ s, if σ i then φ i w = true else φ i w = false)

private theorem anchorOnFinset_empty {ι : Type*} [DecidableEq ι]
    (φ : ι → W → Bool) (σ : ι → Bool) :
    anchorOnFinset φ σ ∅ = (⊤ : W → Bool) := by
  funext w
  simp [anchorOnFinset]

private theorem anchorOnFinset_insert {ι : Type*} [DecidableEq ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (i : ι) (s : Finset ι) :
    anchorOnFinset φ σ (insert i s) =
    anchorOnFinset φ σ s ⊓ (if σ i then φ i else (φ i)ᶜ) := by
  funext w
  show decide _ = _
  rw [decide_eq_decide.mpr (Finset.forall_mem_insert (s := s) (a := i)
        (p := fun j => if σ j then φ j w = true else φ j w = false))]
  rw [Bool.decide_and, Bool.and_comm, Pi.inf_apply]
  congr 1
  cases hi : σ i <;> simp

private theorem anchorOnFinset_mem_closure {ι : Type*} [DecidableEq ι] [Fintype ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (s : Finset ι) :
    anchorOnFinset φ σ s ∈ BooleanSubalgebra.closure (Set.range φ) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [anchorOnFinset_empty]
    exact (BooleanSubalgebra.closure (Set.range φ)).top_mem
  | insert i s his ih =>
    rw [anchorOnFinset_insert φ σ i s]
    exact (BooleanSubalgebra.closure (Set.range φ)).infClosed' ih
      (lit_mem_closure φ σ i)

/-- Anchor formulas lie in the Boolean closure of `Set.range φ`. -/
theorem anchor_mem_closure {ι : Type*} [DecidableEq ι] [Fintype ι]
    (φ : ι → W → Bool) (σ : ι → Bool) :
    anchor φ σ ∈ BooleanSubalgebra.closure (Set.range φ) := by
  have hEq : anchor φ σ = anchorOnFinset φ σ Finset.univ := by
    funext w
    unfold anchor anchorOnFinset
    congr 1
    exact propext ⟨fun h i _ => h i, fun h i => h i (Finset.mem_univ i)⟩
  rw [hEq]
  exact anchorOnFinset_mem_closure φ σ Finset.univ

/-! ### Atoms of the closure -/

/-- A consistent anchor cell is an atom of `closure (Set.range φ)`: it is below or
disjoint from every closure element (Lemma 6), so once nonzero nothing lies
strictly between it and `⊥`. -/
theorem isAtom_anchor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (hCons : ∃ w, anchor φ σ w = true) :
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

section WorldEnumeration

variable [Fintype W]

/-! ### Bitstring representation (Definition 7) -/

/-- A positional index for the anchor cells, via `partition.equivFin`. -/
private noncomputable def anchorIndex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) :
    Fin (partition ι W φ).card → (ι → Bool) :=
  fun i => ((partition ι W φ).equivFin.symm i).val

/-- The bitstring of `ψ` relative to `φ`: bit `i` is `true` iff anchor `i` entails
`ψ` (@cite{demey-smessaert-2018}, Definition 7). -/
noncomputable def bitstringOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (ψ : W → Bool) :
    Fin (partition ι W φ).card → Bool :=
  fun i => decide (∀ w, anchor φ (anchorIndex φ i) w = true → ψ w = true)

private theorem anchorIndex_consistent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (i : Fin (partition ι W φ).card) :
    ∃ w, anchor φ (anchorIndex φ i) w = true := by
  classical
  have hMem : ((partition ι W φ).equivFin.symm i).val ∈ partition ι W φ :=
    ((partition ι W φ).equivFin.symm i).property
  unfold partition at hMem
  rw [Finset.mem_filter] at hMem
  simpa [anchorIndex] using hMem.2

/-! ### Bitstring evaluation -/

/-- If `w` satisfies anchor `i` and `ψ` is in the closure, then `bitstringOf φ ψ i`
is `ψ w`. -/
theorem bitstringOf_eq_apply_at_anchor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ))
    (i : Fin (partition ι W φ).card) {w : W}
    (hw : anchor φ (anchorIndex φ i) w = true) :
    bitstringOf φ ψ i = ψ w := by
  rcases anchor_le_or_le_compl_mem_closure φ (anchorIndex φ i) hψ with hL | hR
  · have hβ : bitstringOf φ ψ i = true := by
      unfold bitstringOf
      rw [decide_eq_true_eq]
      exact fun w' hw' => (le_iff_forall.mp hL) w' hw'
    have hψw : ψ w = true := (le_iff_forall.mp hL) w hw
    rw [hβ, hψw]
  · have hψw : ψ w = false := by
      have := (le_iff_forall.mp hR) w hw
      simpa using this
    have hβ : bitstringOf φ ψ i = false := by
      cases hb : bitstringOf φ ψ i
      · rfl
      · exfalso
        unfold bitstringOf at hb
        rw [decide_eq_true_eq] at hb
        rw [hb w hw] at hψw
        exact Bool.noConfusion hψw
    rw [hβ, hψw]

/-- An anchor index satisfied by `w`. -/
noncomputable def worldAnchorIndex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (w : W) : Fin (partition ι W φ).card :=
  let σ := Classical.choose (anchor_jointly_exhaustive φ w)
  let hσ := Classical.choose_spec (anchor_jointly_exhaustive φ w)
  (partition ι W φ).equivFin ⟨σ, by
    unfold partition
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, decide_eq_true ⟨w, hσ⟩⟩⟩

theorem anchor_worldAnchorIndex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (w : W) :
    anchor φ (anchorIndex φ (worldAnchorIndex φ w)) w = true := by
  unfold worldAnchorIndex anchorIndex
  simp only [Equiv.symm_apply_apply]
  exact Classical.choose_spec (anchor_jointly_exhaustive φ w)

/-- `bitstringOf φ ψ` at a world's anchor index recovers `ψ` at that world. -/
theorem bitstringOf_apply_at_world
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) (w : W) :
    bitstringOf φ ψ (worldAnchorIndex φ w) = ψ w :=
  bitstringOf_eq_apply_at_anchor φ hψ _ (anchor_worldAnchorIndex φ w)

/-- `bitstringOf φ` is injective on the Boolean closure. -/
theorem bitstringOf_injOn_closure
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → W → Bool) :
    Set.InjOn (bitstringOf φ)
      (BooleanSubalgebra.closure (Set.range φ) : Set (W → Bool)) := by
  intro ψ₁ hψ₁ ψ₂ hψ₂ hEq
  funext w
  rw [← bitstringOf_apply_at_world φ hψ₁ w, hEq, bitstringOf_apply_at_world φ hψ₂ w]

/-! ### The inverse and round trips -/

/-- The supremum of the anchor cells whose bit is `true` — the inverse of
`bitstringOf` on the closure. -/
noncomputable def bitstringInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (b : Fin (partition ι W φ).card → Bool) : W → Bool :=
  ⨆ i, (if b i then anchor φ (anchorIndex φ i) else (⊥ : W → Bool))

theorem bitstringInverse_mem_closure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (b : Fin (partition ι W φ).card → Bool) :
    bitstringInverse φ b ∈ BooleanSubalgebra.closure (Set.range φ) := by
  unfold bitstringInverse
  apply BooleanSubalgebra.iSup_mem
  intro i
  by_cases h : b i = true
  · simp only [h, ↓reduceIte]
    exact anchor_mem_closure φ _
  · have hf : b i = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact (BooleanSubalgebra.closure (Set.range φ)).bot_mem

private theorem anchorIndex_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) :
    Function.Injective (anchorIndex φ) := by
  intro i j h
  unfold anchorIndex at h
  exact (partition ι W φ).equivFin.symm.injective (Subtype.ext h)

private theorem anchor_at_world_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {i j : Fin (partition ι W φ).card} {w : W}
    (hi : anchor φ (anchorIndex φ i) w = true)
    (hj : anchor φ (anchorIndex φ j) w = true) :
    i = j := by
  by_contra hne
  apply anchor_mutually_exclusive φ (anchorIndex φ i) (anchorIndex φ j)
    (fun heq => hne (anchorIndex_injective φ heq)) w
  exact ⟨hi, hj⟩

/-- If `w` satisfies anchor `j`, then `bitstringInverse φ b w` is the `j`-th bit:
the `iSup` collapses to the summand at `j`. -/
theorem bitstringInverse_apply_at_anchor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (b : Fin (partition ι W φ).card → Bool)
    (j : Fin (partition ι W φ).card) {w : W}
    (hw : anchor φ (anchorIndex φ j) w = true) :
    bitstringInverse φ b w = b j := by
  unfold bitstringInverse
  rw [iSup_apply]
  apply le_antisymm
  · apply iSup_le
    intro i
    by_cases hij : i = j
    · subst hij
      by_cases hbi : b i = true
      · simp [hbi, hw]
      · have : b i = false := Bool.eq_false_iff.mpr hbi
        simp [this]
    · have hf : anchor φ (anchorIndex φ i) w = false := by
        cases hai : anchor φ (anchorIndex φ i) w
        · rfl
        · exact absurd (anchor_at_world_unique φ hai hw) hij
      by_cases hbi : b i = true
      · simp [hbi, hf]
      · have : b i = false := Bool.eq_false_iff.mpr hbi
        simp [this]
  · by_cases hbj : b j = true
    · have h1 : (if b j then anchor φ (anchorIndex φ j) else (⊥ : W → Bool)) w = true := by
        simp [hbj, hw]
      calc b j = true := hbj
        _ = (if b j then anchor φ (anchorIndex φ j) else (⊥ : W → Bool)) w := h1.symm
        _ ≤ ⨆ i, (if b i then anchor φ (anchorIndex φ i) else (⊥ : W → Bool)) w :=
            le_iSup (fun i => (if b i then anchor φ (anchorIndex φ i)
                                       else (⊥ : W → Bool)) w) j
    · have : b j = false := Bool.eq_false_iff.mpr hbj
      rw [this]
      exact Bool.false_le _

theorem bitstringOf_bitstringInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (b : Fin (partition ι W φ).card → Bool) :
    bitstringOf φ (bitstringInverse φ b) = b := by
  funext j
  obtain ⟨w, hw⟩ := anchorIndex_consistent φ j
  rw [bitstringOf_eq_apply_at_anchor φ (bitstringInverse_mem_closure φ b) j hw]
  exact bitstringInverse_apply_at_anchor φ b j hw

theorem bitstringInverse_bitstringOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) :
    bitstringInverse φ (bitstringOf φ ψ) = ψ := by
  funext w
  rw [bitstringInverse_apply_at_anchor φ (bitstringOf φ ψ)
      (worldAnchorIndex φ w) (anchor_worldAnchorIndex φ w)]
  exact bitstringOf_apply_at_world φ hψ w

/-! ### Theorem 1: the Boolean isomorphism -/

/-- **Theorem 1** (@cite{demey-smessaert-2018}): `bitstringOf φ` is an order
isomorphism `closure (Set.range φ) ≃o (Fin n → Bool)`, `n = |partition|`. -/
noncomputable def bitstringOf_orderIso
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → W → Bool) :
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
      rw [bitstringOf_eq_apply_at_anchor φ hψ₁ i hw,
          bitstringOf_eq_apply_at_anchor φ hψ₂ i hw]
      exact h w

/-! ### Theorem 2: Aristotelian transfer

Each relation transfers along the Boolean isomorphism `bitstringOf_orderIso`
(@cite{demey-smessaert-2018}, Theorem 2). -/

section Transfer
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → W → Bool)
  (a b : BooleanSubalgebra.closure (Set.range φ))

theorem isContradictory_bitstring_iff :
    IsContradictory (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsContradictory a b :=
  isContradictory_apply_orderIso (bitstringOf_orderIso φ)

theorem isContrary_bitstring_iff :
    IsContrary (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsContrary a b :=
  isContrary_apply_orderIso (bitstringOf_orderIso φ)

theorem isSubcontrary_bitstring_iff :
    IsSubcontrary (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsSubcontrary a b :=
  isSubcontrary_apply_orderIso (bitstringOf_orderIso φ)

theorem isSubaltern_bitstring_iff :
    IsSubaltern (bitstringOf φ a.val) (bitstringOf φ b.val) ↔ IsSubaltern a b :=
  isSubaltern_apply_orderIso (bitstringOf_orderIso φ)

end Transfer

end WorldEnumeration

end Aristotelian

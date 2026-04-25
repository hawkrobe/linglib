import Linglib.Core.Logic.Opposition.Partition
import Linglib.Core.Logic.Opposition.Atoms
import Mathlib.Data.Fintype.Order
import Mathlib.Order.BooleanSubalgebra

/-!
# Bitstring semantics for logical fragments (skeleton)

Per @cite{demey-smessaert-2018} §3.2, Definition 7 and Theorems 1–2.

Given a fragment `ℱ` with partition `Π_S(ℱ) = {α_1, ..., α_n}`, the bitstring
semantics `β_S^ℱ : 𝔹(ℱ) → BitVec n` assigns each formula in the Boolean
closure of ℱ a bitstring whose `i`-th position is `1` iff the anchor
formula `α_i` entails it:

  [β_S^ℱ(φ)]_i := 1 iff ⊨_S α_i → φ

**Theorem 1**: `β_S^ℱ` is a Boolean-algebra isomorphism.
**Theorem 2**: `β_S^ℱ` is therefore an Aristotelian isomorphism (Lemma 1).

The Aristotelian relations on bitstrings (Definition 2) are bitwise:

| Relation       | Bitstring condition          |
|----------------|------------------------------|
| Contradictory  | `b₁ ∧ b₂ = 0` and `b₁ ∨ b₂ = 1` |
| Contrary       | `b₁ ∧ b₂ = 0` and `b₁ ∨ b₂ ≠ 1` |
| Subcontrary    | `b₁ ∧ b₂ ≠ 0` and `b₁ ∨ b₂ = 1` |
| Subaltern      | `b₁ ∧ b₂ = b₁` and `b₁ ∨ b₂ ≠ b₁` |

## What's here

- `bitstringOf φ ψ` — Definition 7 (the bit at index `i` says whether anchor
  `α_i` entails `ψ`)
- `BitContradictory`/`BitContrary`/`BitSubcontrary`/`BitSubaltern` —
  Definition 2 (Aristotelian relations on bitstrings)
- `bitstringOf_orderIso : closure (Set.range φ) ≃o (Fin n → Bool)` —
  **Theorem 1** (Boolean-algebra isomorphism), §11
- `contradictory_iff_bitContradictory` and three siblings — **Theorem 2**
  (Aristotelian relations transfer), §10
-/

namespace Core.Opposition

variable {W : Type*} [Fintype W]

-- ============================================================================
-- §1. Bitstring representation (Definition 7)
-- ============================================================================

/-- Index a Finset by a Fin, giving each anchor formula a positional index.
    The choice of indexing is arbitrary up to permutation; downstream
    Aristotelian relations are invariant under it. -/
private noncomputable def anchorIndex {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) :
    Fin (partition ι W φ).card → (ι → Bool) :=
  fun i => ((partition ι W φ).equivFin.symm i).val

/-- The bitstring of a Boolean predicate `ψ` relative to a fragment `φ`:
    bit `i` is `true` iff anchor formula `i` entails `ψ`. -/
noncomputable def bitstringOf {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (ψ : W → Bool) :
    Fin (partition ι W φ).card → Bool :=
  fun i => decide (∀ w, anchor φ (anchorIndex φ i) w = true → ψ w = true)

-- ============================================================================
-- §2. Aristotelian relations on bitstrings (Definition 2)
-- ============================================================================

/-- Bitwise AND. -/
def bitAnd {n : ℕ} (b₁ b₂ : Fin n → Bool) : Fin n → Bool :=
  fun i => b₁ i && b₂ i

/-- Bitwise OR. -/
def bitOr {n : ℕ} (b₁ b₂ : Fin n → Bool) : Fin n → Bool :=
  fun i => b₁ i || b₂ i

/-- All-zeros bitstring. -/
def zeros (n : ℕ) : Fin n → Bool := fun _ => false

/-- All-ones bitstring. -/
def ones (n : ℕ) : Fin n → Bool := fun _ => true

@[simp] lemma bitAnd_apply {n : ℕ} (b₁ b₂ : Fin n → Bool) (i : Fin n) :
    bitAnd b₁ b₂ i = (b₁ i && b₂ i) := rfl

@[simp] lemma bitOr_apply {n : ℕ} (b₁ b₂ : Fin n → Bool) (i : Fin n) :
    bitOr b₁ b₂ i = (b₁ i || b₂ i) := rfl

@[simp] lemma zeros_apply {n : ℕ} (i : Fin n) : zeros n i = false := rfl

@[simp] lemma ones_apply {n : ℕ} (i : Fin n) : ones n i = true := rfl

/-- Bitstring contradictoriness: `b₁ ∧ b₂ = 0` and `b₁ ∨ b₂ = 1`. -/
def BitContradictory {n : ℕ} (b₁ b₂ : Fin n → Bool) : Prop :=
  bitAnd b₁ b₂ = zeros n ∧ bitOr b₁ b₂ = ones n

/-- Bitstring contrariety: `b₁ ∧ b₂ = 0` and `b₁ ∨ b₂ ≠ 1`. -/
def BitContrary {n : ℕ} (b₁ b₂ : Fin n → Bool) : Prop :=
  bitAnd b₁ b₂ = zeros n ∧ bitOr b₁ b₂ ≠ ones n

/-- Bitstring subcontrariety: `b₁ ∧ b₂ ≠ 0` and `b₁ ∨ b₂ = 1`. -/
def BitSubcontrary {n : ℕ} (b₁ b₂ : Fin n → Bool) : Prop :=
  bitAnd b₁ b₂ ≠ zeros n ∧ bitOr b₁ b₂ = ones n

/-- Bitstring subalternation: `b₁ ⊆ b₂` (bitwise ≤) and not equal. -/
def BitSubaltern {n : ℕ} (b₁ b₂ : Fin n → Bool) : Prop :=
  bitAnd b₁ b₂ = b₁ ∧ bitOr b₁ b₂ ≠ b₁

-- ============================================================================
-- §3. Forward Aristotelian transfer (partial — what goes through without closure)
-- ============================================================================

/-- The anchor at position `i` is consistent: there exists a world satisfying it.
    Extracted from the `partition` Finset's filter membership. -/
private theorem anchorIndex_consistent {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (i : Fin (partition ι W φ).card) :
    ∃ w, anchor φ (anchorIndex φ i) w = true := by
  classical
  have hMem : ((partition ι W φ).equivFin.symm i).val ∈ partition ι W φ :=
    ((partition ι W φ).equivFin.symm i).property
  unfold partition at hMem
  rw [Finset.mem_filter] at hMem
  simpa [anchorIndex] using hMem.2

/-- **Forward direction of Theorem 2 (bitAnd half)**: Boolean contradictoriness
    of two arbitrary `W → Bool` predicates implies their bitstrings have empty
    bitwise-AND. This direction goes through without Boolean-closure
    infrastructure — only the partition's anchor-consistency matters.

    The reverse direction (`BitContradictory → Contradictory`) and the
    bitOr-direction (`Contradictory → bitOr = ones`) require the Boolean-closure
    precondition (Demey-Smessaert §3, Lemma 6: every `φ ∈ 𝔹(ℱ)` is
    anchor-decided), which would in turn need Theorem 1's Boolean-algebra
    structure on `𝔹(ℱ)`. -/
theorem bitAnd_bitstringOf_eq_zeros_of_contradictory
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {ψ₁ ψ₂ : W → Bool} (h : Contradictory ψ₁ ψ₂) :
    bitAnd (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) = zeros _ := by
  funext i
  unfold bitAnd zeros
  obtain ⟨w, hw⟩ := anchorIndex_consistent φ i
  by_cases h1 : bitstringOf φ ψ₁ i = true
  · by_cases h2 : bitstringOf φ ψ₂ i = true
    · exfalso
      unfold bitstringOf at h1 h2
      rw [decide_eq_true_eq] at h1 h2
      exact h.1 w ⟨h1 w hw, h2 w hw⟩
    · simp [h1, h2]
  · simp [h1]

-- ============================================================================
-- §4. Bridge: `anchor` in the `W → Bool` BooleanAlgebra
-- ============================================================================

/-- Pointwise reduction of `≤` in `W → Bool`: `f ≤ g` iff `f w = true → g w = true`
    everywhere. Standard `Pi.le_def` instantiation for `Bool`-valued functions. -/
private lemma le_iff_pointwise_imp {f g : W → Bool} :
    f ≤ g ↔ ∀ w, f w = true → g w = true := by
  rw [Pi.le_def]
  refine forall_congr' fun w => ?_
  cases f w <;> cases g w <;> simp <;> decide

/-- Lemma 6 specialized to our indexed-family `anchor`: every `ψ` in the Boolean
    closure of `Set.range φ` is anchor-decided. Direct induction on closure.

    **Note**: `Atoms.lean::anchorBA_le_or_le_compl_mem_closure` proves the same
    statement for the BA-generic `anchorBA s σ` form (`s : Finset α`, `σ : s → Bool`).
    The two are not directly bridged: the bridge would require `Finset.image φ`
    to collapse duplicate generators and a corresponding choice of polarity per
    duplicate-class — adding case analysis that exceeds the cost of just
    reproving the specialized form here. The structural proof (induction on
    `closure_bot_sup_induction`) is the same in both files; if either changes,
    so does the other. -/
theorem anchor_le_or_le_compl_mem_closure
    {ι : Type} [Fintype ι] (φ : ι → W → Bool) (σ : ι → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) :
    anchor φ σ ≤ ψ ∨ anchor φ σ ≤ ψᶜ := by
  induction hψ using BooleanSubalgebra.closure_bot_sup_induction with
  | mem ψ' hψ' =>
    obtain ⟨i, rfl⟩ := hψ'
    by_cases h : σ i = true
    · left
      rw [le_iff_pointwise_imp]
      intro w hw
      unfold anchor at hw
      rw [decide_eq_true_eq] at hw
      have := hw i
      rw [if_pos h] at this
      exact this
    · right
      rw [le_iff_pointwise_imp]
      intro w hw
      have hf : σ i = false := Bool.eq_false_iff.mpr h
      unfold anchor at hw
      rw [decide_eq_true_eq] at hw
      have := hw i
      rw [if_neg h] at this
      simp [this]
  | bot =>
    right
    rw [le_iff_pointwise_imp]
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

-- §5. Theorem 1 statement is now `bitstringOf_orderIso` in §11 (the full
-- bidirectional Boolean-algebra isomorphism). The supporting infrastructure
-- (master bridge, anchor_mem_closure, bitstringInverse, round trips) is
-- built up in §6-§10 below.

-- ============================================================================
-- §6. Master bridge: bitstringOf at a world equals ψ at that world
-- ============================================================================

/-- **The bridge lemma**: for any `ψ` in the Boolean closure and any world `w`
    that satisfies the anchor at index `i`, the bit `bitstringOf φ ψ i` equals
    `ψ w`. This is the well-definedness of the bitstring representation:
    Lemma 6 (anchor-decidedness) plus consistency means every anchor-witness
    world agrees on `ψ`'s truth value, so the bit is unambiguous.

    All four Aristotelian-relation theorems below are corollaries of this
    lemma + partition exhaustion. -/
theorem bitstringOf_eq_apply_at_anchor
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ))
    (i : Fin (partition ι W φ).card) {w : W}
    (hw : anchor φ (anchorIndex φ i) w = true) :
    bitstringOf φ ψ i = ψ w := by
  rcases anchor_le_or_le_compl_mem_closure φ (anchorIndex φ i) hψ with hL | hR
  · -- anchor ≤ ψ: both bit and ψ w are true
    have hβ : bitstringOf φ ψ i = true := by
      unfold bitstringOf
      rw [decide_eq_true_eq]
      exact fun w' hw' => (le_iff_pointwise_imp.mp hL) w' hw'
    have hψw : ψ w = true := (le_iff_pointwise_imp.mp hL) w hw
    rw [hβ, hψw]
  · -- anchor ≤ ψᶜ: both bit and ψ w are false
    have hψw : ψ w = false := by
      have := (le_iff_pointwise_imp.mp hR) w hw
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

/-- For each world, the index of an anchor it satisfies (chosen via Classical
    on `anchor_jointly_exhaustive`). Composes with `bitstringOf_eq_apply_at_anchor`
    to give `bitstringOf φ ψ (worldAnchorIndex φ w) = ψ w`. -/
noncomputable def worldAnchorIndex {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (w : W) : Fin (partition ι W φ).card :=
  let σ := Classical.choose (anchor_jointly_exhaustive φ w)
  let hσ := Classical.choose_spec (anchor_jointly_exhaustive φ w)
  (partition ι W φ).equivFin ⟨σ, by
    unfold partition
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, decide_eq_true ⟨w, hσ⟩⟩⟩

/-- The anchor at `worldAnchorIndex φ w` is satisfied by `w`. -/
theorem anchor_worldAnchorIndex {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (w : W) :
    anchor φ (anchorIndex φ (worldAnchorIndex φ w)) w = true := by
  unfold worldAnchorIndex anchorIndex
  simp only [Equiv.symm_apply_apply]
  exact Classical.choose_spec (anchor_jointly_exhaustive φ w)

/-- **The world-side bridge**: at any world, `bitstringOf φ ψ` evaluated at
    that world's anchor index returns `ψ` at that world. Direct corollary of
    `bitstringOf_eq_apply_at_anchor` + `anchor_worldAnchorIndex`. -/
theorem bitstringOf_apply_at_world
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) (w : W) :
    bitstringOf φ ψ (worldAnchorIndex φ w) = ψ w :=
  bitstringOf_eq_apply_at_anchor φ hψ _ (anchor_worldAnchorIndex φ w)

/-- **Theorem 1's injectivity half**: `bitstringOf φ` is injective on the
    Boolean closure. Two formulas in the closure with the same bitstring
    representation agree at every world.

    One-line proof: at each `w`, `ψ_j w = bitstringOf φ ψ_j (worldAnchorIndex φ w)`
    for both `j ∈ {1, 2}`, and the bitstrings are equal by hypothesis. -/
theorem bitstringOf_injOn_closure
    {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → W → Bool) :
    Set.InjOn (bitstringOf φ)
      (BooleanSubalgebra.closure (Set.range φ) : Set (W → Bool)) := by
  intro ψ₁ hψ₁ ψ₂ hψ₂ hEq
  funext w
  rw [← bitstringOf_apply_at_world φ hψ₁ w, hEq, bitstringOf_apply_at_world φ hψ₂ w]

-- ============================================================================
-- §7. anchor formulas live in the closure (the surjectivity prerequisite)
-- ============================================================================

/-- A literal `lit (φ i) (σ i)` (positive when `σ i = true`, negative otherwise)
    lies in the Boolean closure of `Set.range φ`. -/
private theorem lit_mem_closure {ι : Type} [Fintype ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (i : ι) :
    (if σ i then φ i else (φ i)ᶜ) ∈
    BooleanSubalgebra.closure (Set.range φ) := by
  by_cases h : σ i = true
  · simp only [h, ↓reduceIte]
    exact BooleanSubalgebra.subset_closure ⟨i, rfl⟩
  · have hf : σ i = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact BooleanSubalgebra.compl_mem (BooleanSubalgebra.subset_closure ⟨i, rfl⟩)

/-- The "anchor over a Finset" form of our `anchor` predicate. Used as the
    induction target for `anchor_mem_closure` — the bridge from `decide (∀ i : ι, ...)`
    to a Finset-indexed conjunction. -/
private def anchorOnFinset {ι : Type} [DecidableEq ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (s : Finset ι) : W → Bool :=
  fun w => decide (∀ i ∈ s, if σ i then φ i w = true else φ i w = false)

/-- The empty-Finset anchor is `⊤` (vacuously true). -/
private theorem anchorOnFinset_empty {ι : Type} [DecidableEq ι]
    (φ : ι → W → Bool) (σ : ι → Bool) :
    anchorOnFinset φ σ ∅ = (⊤ : W → Bool) := by
  funext w
  simp [anchorOnFinset]

/-- Insert step: the anchor over `insert i s` decomposes as the anchor over `s`
    meet the literal at `i`. -/
private theorem anchorOnFinset_insert {ι : Type} [DecidableEq ι]
    (φ : ι → W → Bool) (σ : ι → Bool) (i : ι) (s : Finset ι) :
    anchorOnFinset φ σ (insert i s) =
    anchorOnFinset φ σ s ⊓ (if σ i then φ i else (φ i)ᶜ) := by
  funext w
  show decide _ = _
  -- Use decide_eq_decide to lift the bounded-forall iff under decide
  rw [decide_eq_decide.mpr (Finset.forall_mem_insert (s := s) (a := i)
        (p := fun j => if σ j then φ j w = true else φ j w = false))]
  rw [Bool.decide_and, Bool.and_comm]
  -- Evaluate Pi-inf at w: (a ⊓ b) w = a w && b w
  rw [Pi.inf_apply]
  -- Now both sides are && of two Bool atoms
  congr 1
  cases hi : σ i <;> simp [hi]

/-- The Finset-indexed anchor lies in the Boolean closure, by induction on the
    Finset. Used to prove `anchor_mem_closure` for the Fintype.univ case. -/
private theorem anchorOnFinset_mem_closure {ι : Type} [DecidableEq ι] [Fintype ι]
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

/-- **Anchor formulas live in the Boolean closure.** This is the key Layer-3
    bridge: our `decide (∀ i : ι, ...)` form of `anchor` (from `Partition.lean`)
    matches the Finset-indexed anchor over `Finset.univ`, which lives in the
    closure by induction. -/
theorem anchor_mem_closure {ι : Type} [DecidableEq ι] [Fintype ι]
    (φ : ι → W → Bool) (σ : ι → Bool) :
    anchor φ σ ∈ BooleanSubalgebra.closure (Set.range φ) := by
  have hEq : anchor φ σ = anchorOnFinset φ σ Finset.univ := by
    funext w
    unfold anchor anchorOnFinset
    congr 1
    exact propext ⟨fun h i _ => h i, fun h i => h i (Finset.mem_univ i)⟩
  rw [hEq]
  exact anchorOnFinset_mem_closure φ σ Finset.univ

-- ============================================================================
-- §8. The inverse: bitstringInverse and round trips
-- ============================================================================

/-- The inverse of `bitstringOf` on the Boolean closure: takes a bitstring `b`
    to the Boolean-algebra supremum of those anchor formulas whose bit is `true`.
    The result lies in the closure (sup of closure elements via `iSup_mem`). -/
noncomputable def bitstringInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (b : Fin (partition ι W φ).card → Bool) : W → Bool :=
  ⨆ i, (if b i then anchor φ (anchorIndex φ i) else (⊥ : W → Bool))

theorem bitstringInverse_mem_closure {ι : Type} [Fintype ι] [DecidableEq ι]
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

/-- `anchorIndex` is injective: distinct indices give distinct polarity
    assignments (since `equivFin.symm` is a bijection from `Fin n` to a subtype). -/
private theorem anchorIndex_injective {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) :
    Function.Injective (anchorIndex φ) := by
  intro i j h
  unfold anchorIndex at h
  exact (partition ι W φ).equivFin.symm.injective (Subtype.ext h)

/-- **Uniqueness of anchor at a world**: at each world, the anchor at any
    consistent index that holds at the world is *uniquely* this index. Combines
    `anchor_mutually_exclusive` (Partition) with `anchorIndex_injective`. -/
private theorem anchor_at_world_unique
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {i j : Fin (partition ι W φ).card} {w : W}
    (hi : anchor φ (anchorIndex φ i) w = true)
    (hj : anchor φ (anchorIndex φ j) w = true) :
    i = j := by
  by_contra hne
  apply anchor_mutually_exclusive φ (anchorIndex φ i) (anchorIndex φ j)
    (fun heq => hne (anchorIndex_injective φ heq)) w
  exact ⟨hi, hj⟩

/-- **The bitstringInverse-evaluation lemma**: at a world `w` satisfying the
    anchor at index `j`, the inverse bitstring evaluates to the `j`-th bit.
    Heart of both round trips: shows that the `iSup` collapses to a single
    summand (the one at `j`) by uniqueness of the satisfied anchor. -/
theorem bitstringInverse_apply_at_anchor
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (b : Fin (partition ι W φ).card → Bool)
    (j : Fin (partition ι W φ).card) {w : W}
    (hw : anchor φ (anchorIndex φ j) w = true) :
    bitstringInverse φ b w = b j := by
  unfold bitstringInverse
  rw [iSup_apply]
  apply le_antisymm
  · -- ≤ direction: every summand at w is ≤ b j
    apply iSup_le
    intro i
    by_cases hij : i = j
    · subst hij
      by_cases hbi : b i = true
      · simp [hbi, hw]
      · have : b i = false := Bool.eq_false_iff.mpr hbi
        simp [this]
    · -- i ≠ j: anchor σᵢ w = false by uniqueness
      have hf : anchor φ (anchorIndex φ i) w = false := by
        cases hai : anchor φ (anchorIndex φ i) w
        · rfl
        · exact absurd (anchor_at_world_unique φ hai hw) hij
      by_cases hbi : b i = true
      · simp [hbi, hf]
      · have : b i = false := Bool.eq_false_iff.mpr hbi
        simp [this]
  · -- ≥ direction: the j-th summand at w equals b j
    by_cases hbj : b j = true
    · -- bj=true: j-th summand at w = anchor σⱼ w = true = b j
      have h1 : (if b j then anchor φ (anchorIndex φ j) else (⊥ : W → Bool)) w = true := by
        simp [hbj, hw]
      calc b j = true := hbj
        _ = (if b j then anchor φ (anchorIndex φ j) else (⊥ : W → Bool)) w := h1.symm
        _ ≤ ⨆ i, (if b i then anchor φ (anchorIndex φ i) else (⊥ : W → Bool)) w :=
            le_iSup (fun i => (if b i then anchor φ (anchorIndex φ i)
                                       else (⊥ : W → Bool)) w) j
    · -- bj=false: anything ≤ ⨆
      have : b j = false := Bool.eq_false_iff.mpr hbj
      rw [this]
      exact Bool.false_le _

/-- Round trip 1: `bitstringOf ∘ bitstringInverse = id` on `Fin n → Bool`.
    Use `bitstringOf_eq_apply_at_anchor` (lifting through any anchor witness)
    + `bitstringInverse_apply_at_anchor` (evaluating the inverse). -/
theorem bitstringOf_bitstringInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) (b : Fin (partition ι W φ).card → Bool) :
    bitstringOf φ (bitstringInverse φ b) = b := by
  funext j
  obtain ⟨w, hw⟩ := anchorIndex_consistent φ j
  rw [bitstringOf_eq_apply_at_anchor φ (bitstringInverse_mem_closure φ b) j hw]
  exact bitstringInverse_apply_at_anchor φ b j hw

/-- Round trip 2: `bitstringInverse ∘ bitstringOf = id` on closure elements.
    Symmetric to round trip 1, using `bitstringOf_apply_at_world` for evaluation
    of `bitstringOf ψ` at the worldAnchorIndex. -/
theorem bitstringInverse_bitstringOf {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → W → Bool) {ψ : W → Bool}
    (hψ : ψ ∈ BooleanSubalgebra.closure (Set.range φ)) :
    bitstringInverse φ (bitstringOf φ ψ) = ψ := by
  funext w
  rw [bitstringInverse_apply_at_anchor φ (bitstringOf φ ψ)
      (worldAnchorIndex φ w) (anchor_worldAnchorIndex φ w)]
  exact bitstringOf_apply_at_world φ hψ w

-- ============================================================================
-- §11. Theorem 1 — the Boolean isomorphism (full ≃o)
-- ============================================================================

/-- **Theorem 1 (Demey & Smessaert 2018) — the full Boolean-algebra isomorphism**.
    `bitstringOf φ` restricted to the Boolean closure of `Set.range φ` is an
    order isomorphism onto `Fin n → Bool` where `n = |partition|`. As an
    OrderIso between Boolean algebras, it is automatically a Boolean-algebra
    isomorphism (BA structure is determined by the order).

    Construction: `toFun := bitstringOf φ`, `invFun := bitstringInverse φ`,
    round trips established above; monotonicity from
    `bitAnd_eq_left_iff_forall_imp` (entailment ↔ bitwise inclusion). -/
noncomputable def bitstringOf_orderIso
    {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → W → Bool) :
    BooleanSubalgebra.closure (Set.range φ) ≃o
    (Fin (partition ι W φ).card → Bool) where
  toFun := fun ⟨ψ, _⟩ => bitstringOf φ ψ
  invFun := fun b => ⟨bitstringInverse φ b, bitstringInverse_mem_closure φ b⟩
  left_inv := fun ⟨ψ, hψ⟩ => Subtype.ext (bitstringInverse_bitstringOf φ hψ)
  right_inv := fun b => bitstringOf_bitstringInverse φ b
  map_rel_iff' := by
    rintro ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    show bitstringOf φ ψ₁ ≤ bitstringOf φ ψ₂ ↔ ψ₁ ≤ ψ₂
    rw [le_iff_pointwise_imp (f := bitstringOf φ ψ₁) (g := bitstringOf φ ψ₂),
        le_iff_pointwise_imp (f := ψ₁) (g := ψ₂)]
    -- Note: this proof structure parallels `bitAnd_eq_left_iff_forall_imp` (§9)
    -- but is independent: §11 (Theorem 1, here) precedes §9 in file order
    -- because §10's iff theorems use `bitstringOf_orderIso`-related machinery.
    -- A unification (lift §11 to after §9) would save ~10 LOC; deferred.
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

-- ============================================================================
-- §9. Three iff lemmas: bit-level conditions ↔ pointwise predicates
-- ============================================================================

/-! All four Aristotelian-relation theorems below reduce to combinations of
three iff lemmas. Each `Bit*` predicate decomposes into bit-level conditions,
and each bit-level condition matches a pointwise predicate via the bridge
`bitstringOf_eq_apply_at_anchor` (forward) and `bitstringOf_apply_at_world`
(reverse). -/

section IffLemmas

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (φ : ι → W → Bool) {ψ₁ ψ₂ : W → Bool}
  (hψ₁ : ψ₁ ∈ BooleanSubalgebra.closure (Set.range φ))
  (hψ₂ : ψ₂ ∈ BooleanSubalgebra.closure (Set.range φ))

include hψ₁ hψ₂ in
theorem bitAnd_eq_zeros_iff_forall_not_and :
    bitAnd (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) = zeros _ ↔
    ∀ w, ¬ (ψ₁ w = true ∧ ψ₂ w = true) := by
  classical
  refine ⟨fun hAnd w ⟨hw₁, hw₂⟩ => ?_, fun h => ?_⟩
  · have := congrFun hAnd (worldAnchorIndex φ w)
    simp [bitAnd, zeros, bitstringOf_apply_at_world φ hψ₁ w,
          bitstringOf_apply_at_world φ hψ₂ w, hw₁, hw₂] at this
  · funext i
    obtain ⟨w, hw⟩ := anchorIndex_consistent φ i
    simp only [bitAnd, zeros, bitstringOf_eq_apply_at_anchor φ hψ₁ i hw,
               bitstringOf_eq_apply_at_anchor φ hψ₂ i hw]
    have := h w
    cases hw₁ : ψ₁ w <;> cases hw₂ : ψ₂ w <;> simp_all

include hψ₁ hψ₂ in
theorem bitOr_eq_ones_iff_forall_or :
    bitOr (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) = ones _ ↔
    ∀ w, ψ₁ w = true ∨ ψ₂ w = true := by
  classical
  refine ⟨fun hOr w => ?_, fun h => ?_⟩
  · have := congrFun hOr (worldAnchorIndex φ w)
    simp only [bitOr, ones, bitstringOf_apply_at_world φ hψ₁ w,
               bitstringOf_apply_at_world φ hψ₂ w] at this
    cases hw₁ : ψ₁ w <;> cases hw₂ : ψ₂ w <;> simp_all
  · funext i
    obtain ⟨w, hw⟩ := anchorIndex_consistent φ i
    simp only [bitOr, ones, bitstringOf_eq_apply_at_anchor φ hψ₁ i hw,
               bitstringOf_eq_apply_at_anchor φ hψ₂ i hw]
    rcases h w with h | h <;> simp [h]

include hψ₁ hψ₂ in
theorem bitAnd_eq_left_iff_forall_imp :
    bitAnd (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) = bitstringOf φ ψ₁ ↔
    ∀ w, ψ₁ w = true → ψ₂ w = true := by
  classical
  refine ⟨fun hAnd w hw₁ => ?_, fun h => ?_⟩
  · have := congrFun hAnd (worldAnchorIndex φ w)
    simp [bitAnd, bitstringOf_apply_at_world φ hψ₁ w,
          bitstringOf_apply_at_world φ hψ₂ w, hw₁] at this
    exact this
  · funext i
    obtain ⟨w, hw⟩ := anchorIndex_consistent φ i
    simp only [bitAnd, bitstringOf_eq_apply_at_anchor φ hψ₁ i hw,
               bitstringOf_eq_apply_at_anchor φ hψ₂ i hw]
    cases hw₁ : ψ₁ w
    · simp
    · simp [h w hw₁]

include hψ₁ hψ₂ in
theorem bitOr_eq_left_iff_forall_imp_rev :
    bitOr (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) = bitstringOf φ ψ₁ ↔
    ∀ w, ψ₂ w = true → ψ₁ w = true := by
  classical
  refine ⟨fun hOr w hw₂ => ?_, fun h => ?_⟩
  · have := congrFun hOr (worldAnchorIndex φ w)
    simp [bitOr, bitstringOf_apply_at_world φ hψ₁ w,
          bitstringOf_apply_at_world φ hψ₂ w, hw₂] at this
    cases hw₁ : ψ₁ w
    · rw [hw₁] at this; simpa using this
    · rfl
  · funext i
    obtain ⟨w, hw⟩ := anchorIndex_consistent φ i
    simp only [bitOr, bitstringOf_eq_apply_at_anchor φ hψ₁ i hw,
               bitstringOf_eq_apply_at_anchor φ hψ₂ i hw]
    cases hw₂ : ψ₂ w
    · simp
    · simp [h w hw₂]

end IffLemmas

-- ============================================================================
-- §10. Theorem 2 — Aristotelian relations transfer (all four cases)
-- ============================================================================

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (φ : ι → W → Bool) {ψ₁ ψ₂ : W → Bool}
  (hψ₁ : ψ₁ ∈ BooleanSubalgebra.closure (Set.range φ))
  (hψ₂ : ψ₂ ∈ BooleanSubalgebra.closure (Set.range φ))

include hψ₁ hψ₂ in
/-- **Theorem 2 — Contradictory** (Demey & Smessaert 2018). -/
theorem contradictory_iff_bitContradictory :
    Contradictory ψ₁ ψ₂ ↔
    BitContradictory (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) := by
  unfold Contradictory BitContradictory
  simp_rw [bitAnd_eq_zeros_iff_forall_not_and φ hψ₁ hψ₂,
           bitOr_eq_ones_iff_forall_or φ hψ₁ hψ₂]

include hψ₁ hψ₂ in
/-- **Theorem 2 — Contrary** (shares bitAnd half with Contradictory). -/
theorem contrary_iff_bitContrary :
    Contrary ψ₁ ψ₂ ↔
    BitContrary (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) := by
  unfold Contrary BitContrary
  exact ((bitAnd_eq_zeros_iff_forall_not_and φ hψ₁ hψ₂).and
    (not_congr (bitOr_eq_ones_iff_forall_or φ hψ₁ hψ₂))).symm

include hψ₁ hψ₂ in
/-- **Theorem 2 — Subcontrary** (dual of Contrary). -/
theorem subcontrary_iff_bitSubcontrary :
    Subcontrary ψ₁ ψ₂ ↔
    BitSubcontrary (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) := by
  unfold Subcontrary BitSubcontrary
  exact ((not_congr (bitAnd_eq_zeros_iff_forall_not_and φ hψ₁ hψ₂)).and
    (bitOr_eq_ones_iff_forall_or φ hψ₁ hψ₂)).symm

include hψ₁ hψ₂ in
/-- **Theorem 2 — Subaltern** (pointwise inclusion ↔ bitwise). -/
theorem subaltern_iff_bitSubaltern :
    Subaltern ψ₁ ψ₂ ↔
    BitSubaltern (bitstringOf φ ψ₁) (bitstringOf φ ψ₂) := by
  unfold Subaltern BitSubaltern
  exact ((bitAnd_eq_left_iff_forall_imp φ hψ₁ hψ₂).and
    (not_congr (bitOr_eq_left_iff_forall_imp_rev φ hψ₁ hψ₂))).symm

end Core.Opposition

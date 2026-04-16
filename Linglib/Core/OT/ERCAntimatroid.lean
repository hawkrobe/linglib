import Linglib.Core.OT.ERC
import Linglib.Core.OT.Antimatroid
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# ERC–Antimatroid Isomorphism

@cite{merchant-riggle-2016} prove that consistent ERC sets over `n`
constraints are isomorphic to antimatroids on `Fin n`. The two maps
`Antimat` (ERCs → antimatroids) and `RCErc` (antimatroids → ERCs) are
mutually inverse homomorphisms preserving entailment/containment.

This means any result about antimatroids transfers to OT: learning
algorithms, typological classification, complexity bounds.

## Key definitions

- `MChain` — maps a consistent ERC set to its feasible sets (Definition 1)
- `Antimat` — maps a consistent ERC set to an antimatroid (Definition 6)
- `RCErc` — maps an antimatroid to an ERC set (Definition 10)

## Lemmas (§ 3)

- `maximalChain_dominance` — prefix sets are downward-closed under dominance
- `MChain.union_closed` — Lemma 3: MChain is union-closed

## Theorems

- `Antimat_entailment` — Theorem 3: entailment → containment (proved)
- `Antimat_RCErc_inv` — Theorem 1 (placeholder)
- `RCErc_Antimat_inv` — Theorem 2 (placeholder)
- `RCErc_entailment` — Theorem 4 (placeholder)

## References

@cite{merchant-riggle-2016} — OT grammars, beyond partial orders:
ERC sets and antimatroids
-/

namespace Core.OT

-- ============================================================================
-- § 1: Maximal Chains (Definition 1)
-- ============================================================================

/-- A **maximal chain** in the power set lattice on `n` elements is a
    sequence of sets `∅ = S₀ ⊂ S₁ ⊂ ... ⊂ Sₙ = Fin n` where each
    set differs from the previous by exactly one element.

    Each maximal chain corresponds to a total order (ranking) on
    `Fin n`: the element added at step `k` is the constraint ranked
    at position `k`. -/
def maximalChain {n : Nat} (r : Ranking n) : Fin (n + 1) → Set (Fin n) :=
  fun k => { i : Fin n | (r.symm i : Nat) < (k : Nat) }

/-- The maximal chain starts at the empty set. -/
theorem maximalChain_zero {n : Nat} (r : Ranking n) :
    maximalChain r ⟨0, Nat.zero_lt_succ n⟩ = ∅ := by
  ext i; simp [maximalChain]

/-- The maximal chain ends at the full set. -/
theorem maximalChain_last {n : Nat} (r : Ranking n) :
    maximalChain r ⟨n, Nat.lt_succ_of_le le_rfl⟩ = Set.univ := by
  ext i; simp [maximalChain]

-- ============================================================================
-- § 2: MChain — ERC Set → Feasible Sets
-- ============================================================================

/-- `MChain E` is the collection of subsets of `Fin n` that appear in
    some maximal chain consistent with ERC set `E`.

    A set `S` is in `MChain(E)` iff there exists a ranking `r` that
    satisfies all ERCs in `E` and a position `k` such that `S` is the
    set of the top-`k` constraints under `r`.

    @cite{merchant-riggle-2016} Definition 1. -/
def MChain {n : Nat} (E : List (ERC n)) : Set (Fin n) → Prop :=
  fun S => ∃ r : Ranking n, ERCSet.satisfiedBy r E ∧
    ∃ k : Fin (n + 1), maximalChain r k = S

-- ============================================================================
-- § 3: Union Closure (Lemma 3)
-- ============================================================================

/-- Prefix sets are downward-closed under dominance: if `w` dominates
    `l` under ranking `r` and `l` is in the prefix set at position `k`,
    then `w` is too (since `r.symm w < r.symm l < k`).

    This is the key insight enabling the direct construction proof of
    union closure: any W-witness for an L-constraint in a prefix set
    must itself be in that prefix set. -/
theorem maximalChain_dominance {n : Nat} (r : Ranking n) (k : Fin (n + 1))
    (w l : Fin n) (hw : dominates r w l) (hl : l ∈ maximalChain r k) :
    w ∈ maximalChain r k := by
  simp only [maximalChain, Set.mem_setOf_eq] at hl ⊢
  unfold dominates at hw; omega

-- Helpers for the union closure construction

open Classical

/-- Count elements in finset `s` ranked strictly below `i` by `r`. -/
private noncomputable def countBelow {n : Nat} (r : Ranking n)
    (s : Finset (Fin n)) (i : Fin n) : Nat :=
  (s.filter (fun j => (r.symm j : Nat) < (r.symm i : Nat))).card

private theorem countBelow_lt_card {n : Nat} (r : Ranking n)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∈ s) :
    countBelow r s i < s.card := by
  unfold countBelow; apply Finset.card_lt_card; constructor
  · exact Finset.filter_subset _ _
  · intro h; have := h hi; simp only [Finset.mem_filter] at this; omega

private theorem countBelow_strict_mono {n : Nat} (r : Ranking n)
    (s : Finset (Fin n)) (a b : Fin n) (ha : a ∈ s) (_hb : b ∈ s)
    (hlt : (r.symm a : Nat) < (r.symm b : Nat)) :
    countBelow r s a < countBelow r s b := by
  unfold countBelow; apply Finset.card_lt_card; constructor
  · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
  · intro hall; have hmem : a ∈ s.filter (fun j => (r.symm j : Nat) < (r.symm b : Nat)) := by
      simp only [Finset.mem_filter]; exact ⟨ha, hlt⟩
    have hh := hall hmem; simp only [Finset.mem_filter] at hh; omega

private theorem countBelow_injOn {n : Nat} (r : Ranking n)
    (s : Finset (Fin n)) (a b : Fin n) (ha : a ∈ s) (hb : b ∈ s)
    (hab : countBelow r s a = countBelow r s b) : a = b := by
  by_contra hne
  have hrsne : (r.symm a : Nat) ≠ (r.symm b : Nat) :=
    fun h => hne (Equiv.injective r.symm (Fin.ext h))
  rcases Nat.lt_or_gt_of_ne hrsne with h | h
  · exact absurd hab (Nat.ne_of_lt (countBelow_strict_mono r s a b ha hb h))
  · exact absurd hab (Nat.ne_of_gt (countBelow_strict_mono r s b a hb ha h))

/-- The prefix set `{ i | r.symm i < k }` has exactly `k` elements. -/
private theorem prefix_card {n : Nat} (r : Ranking n) (k : Fin (n + 1)) :
    (Finset.univ.filter (fun i : Fin n => (r.symm i : Nat) < k.val)).card = k.val := by
  have heq : Finset.univ.filter (fun i : Fin n => (r.symm i : Nat) < k.val) =
      (Finset.univ : Finset (Fin k.val)).image
        (fun j : Fin k.val => r ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp k.isLt)⟩) := by
    ext i; constructor
    · intro hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨(r.symm i).val, hi⟩, by simp⟩
    · intro hi; simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
      obtain ⟨j, hj⟩ := hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hj, Ranking.symm_apply_apply]
      exact j.isLt
  rw [heq]
  have hinj : Function.Injective
    (fun j : Fin k.val => r ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.lt_succ_iff.mp k.isLt)⟩) :=
    fun a b hab => Fin.ext (Fin.mk.inj (Equiv.injective r hab))
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

set_option maxHeartbeats 1600000 in
/-- MChain is closed under union.

    Given `S = maximalChain r₁ k₁` and `T = maximalChain r₂ k₂` with
    both `r₁, r₂` satisfying `E`, construct `r₃` whose prefix set at
    position `k₁ + |T \ S|` equals `S ∪ T`.

    **Construction**: `r₃` orders elements in three blocks:
    1. Elements of `S`, in `r₁`'s order
    2. Elements of `T \ S`, in `r₂`'s order
    3. Remaining elements, in `r₁`'s order

    The position function `f i` assigns each element its rank in `r₃`:
    - For `i ∈ S`: `f i = r₁.symm i` (positions `0` to `k₁ - 1`)
    - For `i ∈ T \ S`: `f i = k₁ + countBelow r₂ (T\S) i`
    - For `i ∉ S ∪ T`: `f i = k₁ + |T\S| + countBelow r₁ rest i`

    The function `f` is injective (within each block by the underlying
    ranking's injectivity; across blocks by disjoint ranges), hence
    bijective on `Fin n` by `Finite.injective_iff_bijective`. The
    merged ranking `r₃` is `(Equiv.ofBijective f).symm`.

    **ERC satisfaction** follows from `maximalChain_dominance`: for any
    ERC `α ∈ E` and L-constraint `l`, the W-witness `w` from the
    ranking that governs `l`'s block is in the same or earlier block,
    so `f w < f l`.

    @cite{merchant-riggle-2016} Lemma 3. -/
theorem MChain.union_closed {n : Nat} (E : List (ERC n))
    (_hcons : ERCSet.consistent E) (S T : Set (Fin n))
    (_hS : MChain E S) (_hT : MChain E T) : MChain E (S ∪ T) := by
  obtain ⟨r₁, hr₁, k₁, hk₁⟩ := _hS
  obtain ⟨r₂, hr₂, k₂, hk₂⟩ := _hT
  subst hk₁; subst hk₂
  -- Block predicates
  let inS := fun i : Fin n => (r₁.symm i : Nat) < k₁.val
  let inT := fun i : Fin n => (r₂.symm i : Nat) < k₂.val
  -- The three finsets partitioning Fin n
  let sS := Finset.univ.filter inS
  let sTmS := Finset.univ.filter (fun i => inT i ∧ ¬inS i)
  let sR := Finset.univ.filter (fun i => ¬inS i ∧ ¬inT i)
  -- Membership
  have in_sTmS : ∀ i, i ∈ sTmS ↔ (inT i ∧ ¬inS i) := fun i => by simp [sTmS]
  have in_sR : ∀ i, i ∈ sR ↔ (¬inS i ∧ ¬inT i) := fun i => by simp [sR]
  -- |S| = k₁
  have hs_card : sS.card = k₁.val := prefix_card r₁ k₁
  -- Partition: sizes sum to n
  have hpart : sS.card + sTmS.card + sR.card = n := by
    have hd : Disjoint sTmS sR := Finset.disjoint_filter.mpr
      (fun i _ h1 h2 => h2.2 h1.1)
    have hu : sTmS ∪ sR = Finset.univ.filter (fun i : Fin n => ¬inS i) := by
      ext i; simp only [sTmS, sR, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]; tauto
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) inS
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have h2 : sTmS.card + sR.card = (Finset.univ.filter (fun i : Fin n => ¬inS i)).card := by
      rw [← hu, Finset.card_union_of_disjoint hd]
    linarith
  -- Position function
  let f : Fin n → Nat := fun i =>
    if inS i then (r₁.symm i : Nat)
    else if inT i then k₁.val + countBelow r₂ sTmS i
    else k₁.val + sTmS.card + countBelow r₁ sR i
  -- f i < n
  have hf_lt : ∀ i, f i < n := by
    intro i; simp only [f]; split_ifs with h1 h2
    · omega
    · have := countBelow_lt_card r₂ sTmS i ((in_sTmS i).mpr ⟨h2, h1⟩); omega
    · have := countBelow_lt_card r₁ sR i ((in_sR i).mpr ⟨h1, h2⟩); omega
  let ff : Fin n → Fin n := fun i => ⟨f i, hf_lt i⟩
  -- Injective
  have hff_inj : Function.Injective ff := by
    intro a b hab; simp only [ff, Fin.mk.injEq] at hab
    by_cases h1a : inS a <;> by_cases h1b : inS b
    · simp only [f, if_pos h1a, if_pos h1b] at hab
      exact Equiv.injective r₁.symm (Fin.ext hab)
    · exfalso; simp only [f, if_pos h1a, if_neg h1b] at hab
      split_ifs at hab with h2b
      · omega
      · have := countBelow_lt_card r₁ sR b ((in_sR b).mpr ⟨h1b, h2b⟩); omega
    · exfalso; simp only [f, if_neg h1a, if_pos h1b] at hab
      split_ifs at hab with h2a
      · omega
      · have := countBelow_lt_card r₁ sR a ((in_sR a).mpr ⟨h1a, h2a⟩); omega
    · simp only [f, if_neg h1a, if_neg h1b] at hab
      by_cases h2a : inT a <;> by_cases h2b : inT b
      · simp only [if_pos h2a, if_pos h2b] at hab
        exact countBelow_injOn r₂ sTmS a b
          ((in_sTmS a).mpr ⟨h2a, h1a⟩) ((in_sTmS b).mpr ⟨h2b, h1b⟩) (by omega)
      · exfalso; simp only [if_pos h2a, if_neg h2b] at hab
        have := countBelow_lt_card r₂ sTmS a ((in_sTmS a).mpr ⟨h2a, h1a⟩)
        have := countBelow_lt_card r₁ sR b ((in_sR b).mpr ⟨h1b, h2b⟩); omega
      · exfalso; simp only [if_neg h2a, if_pos h2b] at hab
        have := countBelow_lt_card r₁ sR a ((in_sR a).mpr ⟨h1a, h2a⟩)
        have := countBelow_lt_card r₂ sTmS b ((in_sTmS b).mpr ⟨h2b, h1b⟩); omega
      · simp only [if_neg h2a, if_neg h2b] at hab
        exact countBelow_injOn r₁ sR a b
          ((in_sR a).mpr ⟨h1a, h2a⟩) ((in_sR b).mpr ⟨h1b, h2b⟩) (by omega)
  -- Bijective, build r₃
  have hff_bij := Finite.injective_iff_bijective.mp hff_inj
  let e := Equiv.ofBijective ff hff_bij
  let r₃ : Ranking n := e.symm
  let k₃ : Fin (n + 1) := ⟨k₁.val + sTmS.card, by omega⟩
  -- r₃.symm = ff
  have hr₃ : ∀ i, r₃.symm i = ff i := by
    intro i; show e.symm.symm i = ff i; simp [Equiv.symm_symm, e]
  -- dominates r₃ w l ↔ f w < f l
  have hdom : ∀ w l, dominates r₃ w l ↔ f w < f l := by
    intro w l; unfold dominates; constructor
    · intro h; rw [hr₃, hr₃] at h; exact h
    · intro h; rw [hr₃, hr₃]; exact h
  -- Prefix set = S ∪ T
  have hprefix : maximalChain r₃ k₃ = maximalChain r₁ k₁ ∪ maximalChain r₂ k₂ := by
    ext i; simp only [maximalChain, Set.mem_setOf_eq, Set.mem_union, k₃]
    rw [show (r₃.symm i : Nat) = (ff i).val from congrArg Fin.val (hr₃ i)]
    simp only [ff, f]; split_ifs with h1 h2
    · exact ⟨fun _ => .inl h1, fun _ => by omega⟩
    · exact ⟨fun _ => .inr h2,
        fun _ => by have := countBelow_lt_card r₂ sTmS i ((in_sTmS i).mpr ⟨h2, h1⟩); omega⟩
    · exact ⟨fun h => by have := countBelow_lt_card r₁ sR i ((in_sR i).mpr ⟨h1, h2⟩); omega,
        fun h => by rcases h with h | h <;> contradiction⟩
  -- ERC satisfaction
  have hsat : ERCSet.satisfiedBy r₃ E := by
    intro α hα l hl_L
    by_cases h1 : inS l
    · -- l ∈ S: use r₁
      obtain ⟨w, hw_W, hw_dom⟩ := hr₁ α hα l hl_L
      have hw_S : inS w := by
        have := maximalChain_dominance r₁ k₁ w l hw_dom
          (show l ∈ maximalChain r₁ k₁ by simp [maximalChain]; exact h1)
        simp [maximalChain] at this; exact this
      exact ⟨w, hw_W, (hdom w l).mpr (by simp only [f, if_pos hw_S, if_pos h1]; exact hw_dom)⟩
    · by_cases h2 : inT l
      · -- l ∈ T\S: use r₂
        obtain ⟨w, hw_W, hw_dom⟩ := hr₂ α hα l hl_L
        have hw_T : inT w := by
          have := maximalChain_dominance r₂ k₂ w l hw_dom
            (show l ∈ maximalChain r₂ k₂ by simp [maximalChain]; exact h2)
          simp [maximalChain] at this; exact this
        refine ⟨w, hw_W, (hdom w l).mpr ?_⟩
        simp only [f, if_neg h1, if_pos h2]
        by_cases hw1 : inS w
        · simp only [if_pos hw1]; omega
        · simp only [if_neg hw1, if_pos hw_T]
          have := countBelow_strict_mono r₂ sTmS w l
            ((in_sTmS w).mpr ⟨hw_T, hw1⟩) ((in_sTmS l).mpr ⟨h2, h1⟩) hw_dom; omega
      · -- l ∈ rest: use r₁
        obtain ⟨w, hw_W, hw_dom⟩ := hr₁ α hα l hl_L
        refine ⟨w, hw_W, (hdom w l).mpr ?_⟩
        simp only [f, if_neg h1, if_neg h2]
        by_cases hw1 : inS w
        · simp only [if_pos hw1]; omega
        · by_cases hw2 : inT w
          · simp only [if_neg hw1, if_pos hw2]
            have := countBelow_lt_card r₂ sTmS w ((in_sTmS w).mpr ⟨hw2, hw1⟩); omega
          · simp only [if_neg hw1, if_neg hw2]
            have := countBelow_strict_mono r₁ sR w l
              ((in_sR w).mpr ⟨hw1, hw2⟩) ((in_sR l).mpr ⟨h1, h2⟩) hw_dom; omega
  exact ⟨r₃, hsat, k₃, hprefix⟩

-- ============================================================================
-- § 4: Antimat — ERC Set → Antimatroid
-- ============================================================================

/-- `Antimat E` maps a consistent ERC set `E` to an antimatroid on
    `Fin n`. The ground set is `Fin n` (the constraint indices), and
    the feasible sets are `MChain(E)` — the subsets that appear in
    maximal chains consistent with `E`.

    @cite{merchant-riggle-2016} Definition 6, Lemma 4. -/
def Antimat {n : Nat} (E : List (ERC n)) (hcons : ERCSet.consistent E) :
    Antimatroid (Fin n) where
  E := Set.univ
  IsFeasible := MChain E
  empty_feasible := by
    obtain ⟨r, hr⟩ := hcons
    exact ⟨r, hr, ⟨0, Nat.zero_lt_succ n⟩, maximalChain_zero r⟩
  feasible_sub := fun _ _ => Set.subset_univ _
  ground_feasible := by
    obtain ⟨r, hr⟩ := hcons
    exact ⟨r, hr, ⟨n, Nat.lt_succ_of_le le_rfl⟩, maximalChain_last r⟩
  augmentation := fun S hS hne => by
    -- S = maximalChain r k for some consistent r and position k.
    -- Since S ≠ Set.univ, k < n, and the next element r(k) can be added.
    obtain ⟨r, hr, k, hk⟩ := hS
    have hkn : k.val < n := by
      by_contra hge; push Not at hge; apply hne; rw [← hk]; ext i
      simp only [maximalChain, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact Nat.lt_of_lt_of_le (r.symm i).isLt (by omega)
    refine ⟨r ⟨k.val, hkn⟩, Set.mem_univ _, ?_, r, hr, ⟨k.val + 1, by omega⟩, ?_⟩
    · -- r(k) ∉ S: its rank position is k, which is not < k
      rw [← hk]; simp only [maximalChain, Set.mem_setOf_eq, Ranking.symm_apply_apply]; omega
    · -- maximalChain r (k+1) = insert r(k) S
      rw [← hk]; ext i; simp only [maximalChain, Set.mem_insert_iff, Set.mem_setOf_eq]
      constructor
      · intro h
        by_cases heq : (r.symm i).val = k.val
        · left
          have hsymm : r.symm i = ⟨k.val, hkn⟩ := Fin.ext heq
          exact (Equiv.apply_symm_apply r i).symm.trans (congrArg r.toFun hsymm)
        · right; omega
      · rintro (rfl | h)
        · simp only [Ranking.symm_apply_apply]; omega
        · omega
  removal := fun S hS hne => by
    -- S = maximalChain r k with k > 0 (since S is nonempty).
    -- Remove element r(k-1) to get maximalChain r (k-1).
    obtain ⟨r, hr, k, hk⟩ := hS
    have hk0 : 0 < k.val := by
      by_contra h; push Not at h
      rw [← hk] at hne; obtain ⟨x, hx⟩ := hne
      simp only [maximalChain, Set.mem_setOf_eq] at hx; omega
    have hkn1 : k.val - 1 < n := by omega
    refine ⟨r ⟨k.val - 1, hkn1⟩, ?_, r, hr, ⟨k.val - 1, by omega⟩, ?_⟩
    · -- r(k-1) ∈ S: its rank position is k-1 < k
      rw [← hk]; simp only [maximalChain, Set.mem_setOf_eq, Ranking.symm_apply_apply]; omega
    · -- S \ {r(k-1)} = maximalChain r (k-1)
      rw [← hk]; ext i; simp only [maximalChain, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        exact ⟨by omega, fun heq => by rw [heq] at h; simp only [Ranking.symm_apply_apply] at h; omega⟩
      · intro ⟨h1, h2⟩
        have : (r.symm i).val ≠ k.val - 1 := by
          intro heq
          have hsymm : r.symm i = ⟨k.val - 1, hkn1⟩ := Fin.ext heq
          exact h2 ((Equiv.apply_symm_apply r i).symm.trans (congrArg r.toFun hsymm))
        omega
  union_closed := fun S T hS hT => MChain.union_closed E hcons S T hS hT

-- ============================================================================
-- § 5: RCErc — Antimatroid → ERC Set
-- ============================================================================

open Classical

/-- `RCErc` maps a rooted circuit of an antimatroid to an ERC.

    Given a rooted circuit `F : S(r)` with root `r` and carrier `S`:
    - `W(α) = S \ {r}` (constraints that must dominate `r`)
    - `L(α) = {r}` (the root)
    - `e(α) = G \ S` (constraints not in the carrier)

    @cite{merchant-riggle-2016} Definition 10. -/
noncomputable def RCErc_single {n : Nat} (A : Antimatroid (Fin n))
    (rc : Antimatroid.RootedCircuit A) : ERC n :=
  fun k =>
    if k ∈ rc.carrier ∧ k ≠ rc.root then .W
    else if k = rc.root then .L
    else .e

-- ============================================================================
-- § 6: Isomorphism Theorems
-- ============================================================================

/-- **Theorem 1** (@cite{merchant-riggle-2016}): `MChain` is the
    inverse of `RCErc`.

    For any antimatroid `A`, `Antimat(RCErc(A)) = A`. That is, if we
    extract the rooted circuits of `A`, convert them to ERCs, and then
    build the antimatroid from those ERCs, we recover `A` exactly. -/
theorem Antimat_RCErc_inv {n : Nat} (_A : Antimatroid (Fin n))
    -- TODO: requires stating RCErc on full antimatroids,
    -- not just single rooted circuits
    : True := trivial

/-- **Theorem 2** (@cite{merchant-riggle-2016}): `RCErc` is the
    inverse of `Antimat`.

    For any consistent ERC set `E`, `RCErc(Antimat(E)) = E`. -/
theorem RCErc_Antimat_inv {n : Nat} (_E : List (ERC n))
    (_hcons : ERCSet.consistent _E)
    -- TODO: requires full RCErc definition
    : True := trivial

/-- **Theorem 3** (@cite{merchant-riggle-2016}): `Antimat` preserves
    entailment.

    If ERC set `E` entails `F` (every ranking satisfying `E` also
    satisfies `F`), then `Antimat(E) ⊆ Antimat(F)` (every feasible
    set of `Antimat(E)` is also feasible in `Antimat(F)`). -/
theorem Antimat_entailment {n : Nat} (E F : List (ERC n))
    (hE : ERCSet.consistent E) (hF : ERCSet.consistent F)
    (h : ERCSet.entails E F) :
    ∀ S, (Antimat E hE).IsFeasible S → (Antimat F hF).IsFeasible S := by
  intro S ⟨r, hr, k, hk⟩
  exact ⟨r, h r hr, k, hk⟩

/-- **Theorem 4** (@cite{merchant-riggle-2016}): `RCErc` preserves
    containment.

    If antimatroid `A ⊆ B` (every feasible set of `A` is feasible in
    `B`), then `RCErc(A)` entails `RCErc(B)`. -/
theorem RCErc_entailment {n : Nat}
    (_A _B : Antimatroid (Fin n))
    -- TODO: requires full RCErc definition
    : True := trivial

end Core.OT

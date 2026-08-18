import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Rat.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Permutation-subset combinatorics

A closed-form count of `Equiv.Perm (Fin n)` filtered by predicates
of the form "the head of a list filtered by `D` lies in `Y`".

## Main results

For any family `S : Finset (Equiv.Perm (Fin n))` closed under
left-multiplication by swaps of elements of `D`:

- `filter_head_in_card_of_swaps`:
  `(# σ ∈ S where head of permDList σ D ∈ Y) × |D| = |S| × |Y ∩ D|`
- `filter_head_in_rate_of_swaps`: the rational form
  `(count / |S|) = |Y ∩ D| / |D|`.

`perm_filter_head_in_card` / `perm_filter_head_in_rate` are the
`S = Finset.univ` specializations (`|S| = n!`), consumed by
`Studies/Zuraw2010.lean` and `Studies/CoetzeePater2011.lean`. The
swap-closed generality serves partially-ordered constraint grammars,
whose consistent-linear-extension sets are swap-closed within a freely
ranked stratum (`winProb_stratified_binary_rate` in
`Phonology/HarmonicGrammar/PartiallyOrderedConstraints.lean`).

## Proof technique

For `y, y' ∈ D`, left-multiplication by `Equiv.swap y y'` preserves
D-membership pointwise and swaps the head element, so it restricts to a
bijection between the head-fibers `{σ ∈ S : head of permDList σ D = y}`
and `{σ ∈ S : … = y'}` whenever `S` is closed under it. All fibers thus
have equal cardinality; summing over `D` (which partitions `S` when `D`
is nonempty) gives `|D| × |fiber| = |S|`.
-/

namespace Core.Optimization.PermSubsetCombinatorics

open Finset

variable {n : ℕ}

-- ============================================================================
-- § 1: permToList and permDList
-- ============================================================================

/-- Subsequence of `List.ofFn ⇑σ` (σ's values in increasing position order)
    filtered to elements of `D`. The head of this list is the σ-image element
    that lies in D and has the smallest preimage index — i.e., the
    highest-ranked constraint in the OT interpretation. -/
def permDList (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) : List (Fin n) :=
  (List.ofFn ⇑σ).filter (· ∈ D)

theorem permDList_nodup (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) :
    (permDList σ D).Nodup :=
  (List.nodup_ofFn.mpr σ.injective).filter _

@[simp]
theorem mem_permDList (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n))
    (x : Fin n) : x ∈ permDList σ D ↔ x ∈ D := by
  simp only [permDList, List.mem_filter, List.mem_ofFn, decide_eq_true_eq,
    and_iff_right_iff_imp]
  exact fun _ => ⟨σ.symm x, σ.apply_symm_apply x⟩

@[simp]
theorem permDList_toFinset (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) :
    (permDList σ D).toFinset = D := by
  ext x
  rw [List.mem_toFinset, mem_permDList]

@[simp]
theorem permDList_length (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) :
    (permDList σ D).length = D.card := by
  rw [← List.toFinset_card_of_nodup (permDList_nodup σ D), permDList_toFinset]

/-- Decompose `List.ofFn ⇑σ` at any position: the list factors as
    `(take k).map σ ++ σ k :: (drop (k+1)).map σ`. -/
theorem ofFn_split_at (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    List.ofFn ⇑σ =
    ((List.finRange n).take k.val).map σ ++ σ k ::
      ((List.finRange n).drop (k.val + 1)).map σ := by
  have h_lt : k.val < (List.finRange n).length := by
    rw [List.length_finRange]; exact k.isLt
  have h_get : (List.finRange n)[k.val]'h_lt = k := by simp [List.getElem_finRange]
  rw [List.ofFn_eq_map]
  conv_lhs => rw [← List.take_append_drop k.val (List.finRange n)]
  rw [List.drop_eq_getElem_cons h_lt, h_get, List.map_append, List.map_cons]

/-- Inverse: if `List.ofFn ⇑σ = pre ++ x :: suf`, then σ at the
    canonical Fin-position `pre.length` equals `x`. -/
theorem apply_of_ofFn_eq_append_cons (σ : Equiv.Perm (Fin n))
    (pre suf : List (Fin n)) (x : Fin n)
    (h_split : List.ofFn ⇑σ = pre ++ x :: suf) (h_pre_lt : pre.length < n) :
    σ ⟨pre.length, h_pre_lt⟩ = x := by
  have h_split_pre := ofFn_split_at σ ⟨pre.length, h_pre_lt⟩
  have h_lhs_pre_len : (((List.finRange n).take pre.length).map σ).length = pre.length := by
    rw [List.length_map, List.length_take, List.length_finRange]
    omega
  have h_combined : ((List.finRange n).take pre.length).map σ ++
      σ ⟨pre.length, h_pre_lt⟩ ::
      ((List.finRange n).drop (pre.length + 1)).map σ = pre ++ x :: suf := by
    rw [← h_split_pre]; exact h_split
  have h_suf_eq : σ ⟨pre.length, h_pre_lt⟩ ::
      ((List.finRange n).drop (pre.length + 1)).map σ = x :: suf :=
    (List.append_inj h_combined h_lhs_pre_len).2
  exact (List.cons.inj h_suf_eq).1

/-- In a decomposition `List.ofFn ⇑σ = pre ++ x :: suf`, the prefix is the
    σ-image of the first `pre.length` positions. -/
theorem take_map_eq_of_ofFn_eq_append_cons (σ : Equiv.Perm (Fin n))
    {pre suf : List (Fin n)} {x : Fin n}
    (h_split : List.ofFn ⇑σ = pre ++ x :: suf) (h_pre_lt : pre.length < n) :
    ((List.finRange n).take pre.length).map ⇑σ = pre := by
  have h_lhs_pre_len : (((List.finRange n).take pre.length).map σ).length = pre.length := by
    rw [List.length_map, List.length_take, List.length_finRange]; omega
  have h_combined : ((List.finRange n).take pre.length).map σ ++
      σ ⟨pre.length, h_pre_lt⟩ ::
      ((List.finRange n).drop (pre.length + 1)).map σ = pre ++ x :: suf := by
    rw [← ofFn_split_at σ ⟨pre.length, h_pre_lt⟩]; exact h_split
  exact (List.append_inj h_combined h_lhs_pre_len).1

/-- Elements of the prefix of a `List.ofFn ⇑σ` decomposition occupy strictly
    earlier positions than the distinguished element. -/
theorem symm_lt_of_ofFn_eq_append_cons (σ : Equiv.Perm (Fin n))
    {pre suf : List (Fin n)} {x y : Fin n}
    (h_split : List.ofFn ⇑σ = pre ++ x :: suf) (hy : y ∈ pre) :
    σ.symm y < σ.symm x := by
  have h_len : (List.ofFn ⇑σ).length = n := List.length_ofFn
  rw [h_split, List.length_append, List.length_cons] at h_len
  have h_pre_lt : pre.length < n := by omega
  rw [← take_map_eq_of_ofFn_eq_append_cons σ h_split h_pre_lt] at hy
  obtain ⟨j, h_j_take, rfl⟩ := List.mem_map.mp hy
  rw [List.mem_take_iff_getElem] at h_j_take
  obtain ⟨idx, h_idx_lt, h_idx_eq⟩ := h_j_take
  simp only [List.getElem_finRange] at h_idx_eq
  have h_idx_lt_pre : idx < pre.length := by
    simp only [List.length_finRange, lt_min_iff] at h_idx_lt
    omega
  have hx_symm : σ.symm x = ⟨pre.length, h_pre_lt⟩ := by
    rw [← apply_of_ofFn_eq_append_cons σ pre suf x h_split h_pre_lt, Equiv.symm_apply_apply]
  rw [Equiv.symm_apply_apply, hx_symm, Fin.lt_def, ← h_idx_eq]
  exact h_idx_lt_pre

/-- Converse of `symm_lt_of_ofFn_eq_append_cons`: a value positioned strictly
    before `x` lies in the prefix. -/
theorem mem_pre_of_symm_lt (σ : Equiv.Perm (Fin n))
    {pre suf : List (Fin n)} {x y : Fin n}
    (h_split : List.ofFn ⇑σ = pre ++ x :: suf)
    (hy : σ.symm y < σ.symm x) : y ∈ pre := by
  have h_len : (List.ofFn ⇑σ).length = n := List.length_ofFn
  rw [h_split, List.length_append, List.length_cons] at h_len
  have h_pre_lt : pre.length < n := by omega
  have hx_symm : σ.symm x = ⟨pre.length, h_pre_lt⟩ := by
    rw [← apply_of_ofFn_eq_append_cons σ pre suf x h_split h_pre_lt, Equiv.symm_apply_apply]
  rw [← take_map_eq_of_ofFn_eq_append_cons σ h_split h_pre_lt]
  refine List.mem_map.mpr ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
  rw [List.mem_take_iff_getElem]
  refine ⟨(σ.symm y).val, ?_, by simp [List.getElem_finRange]⟩
  rw [hx_symm, Fin.lt_def] at hy
  simp only [List.length_finRange, lt_min_iff]
  exact ⟨hy, (σ.symm y).isLt⟩

/-- The head of `permDList σ D` characterized via mathlib's
    `List.find?_eq_some_iff_append`: `head = some x` iff `x ∈ D` and
    `List.ofFn ⇑σ` decomposes as `prefix ++ x :: suffix` where every
    prefix element lies outside `D`. -/
theorem permDList_head_eq_some_iff (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n))
    (x : Fin n) :
    (permDList σ D).head? = some x ↔
    x ∈ D ∧ ∃ pre suf : List (Fin n),
      List.ofFn ⇑σ = pre ++ x :: suf ∧ ∀ y ∈ pre, y ∉ D := by
  unfold permDList
  rw [List.head?_filter, List.find?_eq_some_iff_append]
  constructor
  · rintro ⟨h_x, pre, suf, h_split, h_pre⟩
    refine ⟨by simpa using h_x, pre, suf, h_split, fun y hy => ?_⟩
    have := h_pre y hy
    simpa using this
  · rintro ⟨h_x, pre, suf, h_split, h_pre⟩
    refine ⟨by simpa using h_x, pre, suf, h_split, fun y hy => ?_⟩
    have := h_pre y hy
    simpa using this

/-- If `(permDList σ D).head? = some x` then `x ∈ D` (the head of a
    filtered list lies in the filter set). -/
theorem mem_of_permDList_head?_eq_some {D : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} {x : Fin n}
    (h : (permDList σ D).head? = some x) : x ∈ D := by
  cases h_eq : permDList σ D with
  | nil => rw [h_eq] at h; exact absurd h (by simp)
  | cons z _ =>
    rw [h_eq] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    have h_mem : z ∈ permDList σ D := by rw [h_eq]; exact List.mem_cons_self
    rw [mem_permDList] at h_mem; exact h_mem

/-- For nonempty `D`, the head of `permDList σ D` is always defined and
    lies in `D`. -/
theorem exists_permDList_head?_eq_some {D : Finset (Fin n)} (h_nonempty : D.Nonempty)
    (σ : Equiv.Perm (Fin n)) :
    ∃ y ∈ D, (permDList σ D).head? = some y := by
  cases h_eq : permDList σ D with
  | nil =>
    have h_card : (permDList σ D).length = D.card := permDList_length σ D
    rw [h_eq] at h_card
    have : D.card = 0 := by simpa using h_card.symm
    rw [Finset.card_eq_zero] at this
    rw [this] at h_nonempty
    exact absurd h_nonempty Finset.not_nonempty_empty
  | cons z _ =>
    refine ⟨z, ?_, by simp⟩
    have h_head : (permDList σ D).head? = some z := by rw [h_eq]; rfl
    exact mem_of_permDList_head?_eq_some h_head

/-- **The head of `permDList σ D` is the σ-earliest element of `D`**: `head? =
    some x` iff `x` lies in `D` and no `D`-element occupies an earlier
    position. The position-minimum characterization, complementing the
    decomposition form `permDList_head_eq_some_iff`. -/
theorem permDList_head?_eq_some_iff_min (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n))
    (x : Fin n) :
    (permDList σ D).head? = some x ↔ x ∈ D ∧ ∀ y ∈ D, σ.symm x ≤ σ.symm y := by
  have fwd : ∀ w, (permDList σ D).head? = some w → w ∈ D ∧ ∀ y ∈ D, σ.symm w ≤ σ.symm y := by
    intro w h
    obtain ⟨hwD, pre, suf, h_split, h_pre⟩ := (permDList_head_eq_some_iff σ D w).mp h
    refine ⟨hwD, fun y hyD => ?_⟩
    by_contra hlt
    exact h_pre y (mem_pre_of_symm_lt σ h_split (not_le.mp hlt)) hyD
  refine ⟨fwd x, ?_⟩
  rintro ⟨hxD, hmin⟩
  obtain ⟨z, hzD, hz⟩ := exists_permDList_head?_eq_some ⟨x, hxD⟩ σ
  obtain ⟨-, hzmin⟩ := fwd z hz
  rwa [show x = z from σ.symm.injective (le_antisymm (hmin z hzD) (hzmin x hxD))]

-- ============================================================================
-- § 2: Multiplicative lemma
-- ============================================================================

/-- When `τ` preserves D-membership both ways, the D-image of `τ * σ` is
    the D-image of `σ` with `τ` applied element-wise. Composes mathlib's
    `List.map_ofFn` and `List.filter_map`. -/
theorem permDList_mul_of_preserves_D
    (D : Finset (Fin n)) (σ τ : Equiv.Perm (Fin n))
    (h_pres : ∀ x : Fin n, x ∈ D ↔ τ x ∈ D) :
    permDList (τ * σ) D = (permDList σ D).map τ := by
  unfold permDList
  rw [Equiv.Perm.coe_mul, ← List.map_ofFn, List.filter_map]
  congr 1
  exact List.filter_congr fun x _ => by simpa using (h_pres x).symm

-- ============================================================================
-- § 3: Swap preserves D-membership when both swap targets are in D
-- ============================================================================

/-- `Equiv.swap y y'` preserves `D`-membership pointwise when both `y` and
    `y'` lie in `D`: any element of `D` other than `y, y'` is fixed; `y`
    maps to `y'` and vice versa, both staying in `D`. -/
private lemma swap_preserves_finset {D : Finset (Fin n)} {y y' : Fin n}
    (hy : y ∈ D) (hy' : y' ∈ D) (x : Fin n) :
    x ∈ D ↔ Equiv.swap y y' x ∈ D := by
  by_cases hxy : x = y
  · subst hxy
    rw [Equiv.swap_apply_left]
    exact ⟨fun _ => hy', fun _ => hy⟩
  · by_cases hxy' : x = y'
    · subst hxy'
      rw [Equiv.swap_apply_right]
      exact ⟨fun _ => hy, fun _ => hy'⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hxy hxy']

-- ============================================================================
-- § 4: Equinumerosity of head-fibers via swap bijection
-- ============================================================================

/-- For `y, y' ∈ D` and a family `S` closed under `σ ↦ swap y y' * σ`, the
    fibers `{σ ∈ S : head of permDList σ D = y}` and
    `{σ ∈ S : head of permDList σ D = y'}` have equal cardinality, witnessed
    by the involution `σ ↦ Equiv.swap y y' * σ`. -/
private theorem card_filter_head_fibers_eq {D : Finset (Fin n)}
    {S : Finset (Equiv.Perm (Fin n))} (y y' : Fin n) (hy : y ∈ D) (hy' : y' ∈ D)
    (h_closed : ∀ σ ∈ S, Equiv.swap y y' * σ ∈ S) :
    (S.filter (fun σ => (permDList σ D).head? = some y)).card =
    (S.filter (fun σ => (permDList σ D).head? = some y')).card := by
  apply Finset.card_bij (fun σ _ => Equiv.swap y y' * σ)
  · -- Maps into target fiber
    intros σ hσ
    simp only [Finset.mem_filter] at hσ ⊢
    obtain ⟨hσS, hσh⟩ := hσ
    refine ⟨h_closed σ hσS, ?_⟩
    rw [permDList_mul_of_preserves_D D σ _ (swap_preserves_finset hy hy')]
    cases h_eq : permDList σ D with
    | nil => rw [h_eq] at hσh; exact absurd hσh (by simp)
    | cons z _ =>
      rw [h_eq] at hσh
      simp only [List.head?_cons, Option.some.injEq] at hσh
      subst hσh
      simp only [List.map_cons, List.head?_cons, Equiv.swap_apply_left]
  · -- Injective
    intros σ₁ _ σ₂ _ heq
    exact mul_left_cancel heq
  · -- Surjective
    intros σ' hσ'
    simp only [Finset.mem_filter] at hσ'
    obtain ⟨hσS, hσh⟩ := hσ'
    refine ⟨Equiv.swap y y' * σ', ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨h_closed σ' hσS, ?_⟩
      rw [permDList_mul_of_preserves_D D σ' _ (swap_preserves_finset hy hy')]
      cases h_eq : permDList σ' D with
      | nil => rw [h_eq] at hσh; exact absurd hσh (by simp)
      | cons z _ =>
        rw [h_eq] at hσh
        simp only [List.head?_cons, Option.some.injEq] at hσh
        subst hσh
        simp only [List.map_cons, List.head?_cons, Equiv.swap_apply_right]
    · -- swap is an involution: swap * (swap * σ') = σ'
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

-- ============================================================================
-- § 5: Partition by head over a nonempty D
-- ============================================================================

/-- For nonempty `D`, summing head-fiber cardinalities over `y ∈ D` recovers
    the cardinality of any family `S`, since every σ has its head in `D`. -/
private theorem sum_card_filter_head_eq {D : Finset (Fin n)}
    (S : Finset (Equiv.Perm (Fin n))) (h_nonempty : D.Nonempty) :
    ∑ y ∈ D, (S.filter (fun σ => (permDList σ D).head? = some y)).card = S.card := by
  classical
  have h_disjoint : (↑D : Set (Fin n)).PairwiseDisjoint
      (fun y => S.filter (fun σ => (permDList σ D).head? = some y)) := by
    intros y _ y' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro σ ⟨_, h₁⟩ ⟨_, h₂⟩
    exact hne (Option.some.inj (h₁.symm.trans h₂))
  have h_union : D.biUnion
      (fun y => S.filter (fun σ => (permDList σ D).head? = some y)) = S := by
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨y, _, hσS, _⟩; exact hσS
    · intro hσS
      obtain ⟨y, hyD, hhead⟩ := exists_permDList_head?_eq_some h_nonempty σ
      exact ⟨y, hyD, hσS, hhead⟩
  calc ∑ y ∈ D, (S.filter (fun σ => (permDList σ D).head? = some y)).card
      = (D.biUnion (fun y => S.filter (fun σ =>
          (permDList σ D).head? = some y))).card :=
        (Finset.card_biUnion h_disjoint).symm
    _ = S.card := by rw [h_union]

/-- For `y ∈ D` and swap-closed `S`, the count of `σ ∈ S` whose
    `permDList σ D` starts with `y` is `|S| / |D|`, expressed in multiplied
    form to avoid ℕ division. -/
private theorem card_filter_head_eq_mul {D : Finset (Fin n)}
    {S : Finset (Equiv.Perm (Fin n))} (y : Fin n) (hy : y ∈ D)
    (h_closed : ∀ y₁ ∈ D, ∀ y₂ ∈ D, ∀ σ ∈ S, Equiv.swap y₁ y₂ * σ ∈ S) :
    (S.filter (fun σ => (permDList σ D).head? = some y)).card * D.card = S.card := by
  have h_const : ∀ y' ∈ D,
      (S.filter (fun σ => (permDList σ D).head? = some y')).card =
      (S.filter (fun σ => (permDList σ D).head? = some y)).card :=
    fun y' hy' => card_filter_head_fibers_eq y' y hy' hy (h_closed y' hy' y hy)
  have h_sum := sum_card_filter_head_eq S ⟨y, hy⟩
  rw [Finset.sum_congr rfl h_const, Finset.sum_const, smul_eq_mul] at h_sum
  rw [mul_comm]; exact h_sum

-- ============================================================================
-- § 6: Closed form for "head ∈ Y" predicates
-- ============================================================================

/-- **The closed-form count over a swap-closed family**: for `S` closed under
    left-multiplication by swaps of `D`-elements, the number of `σ ∈ S` whose
    `permDList σ D` head lies in `Y` is `|S| × |Y ∩ D| / |D|`, expressed in
    multiplied form to avoid ℕ division. -/
theorem filter_head_in_card_of_swaps (S : Finset (Equiv.Perm (Fin n)))
    (D Y : Finset (Fin n))
    (h_closed : ∀ y₁ ∈ D, ∀ y₂ ∈ D, ∀ σ ∈ S, Equiv.swap y₁ y₂ * σ ∈ S) :
    (S.filter (fun σ => ∃ x ∈ Y, (permDList σ D).head? = some x)).card * D.card =
    S.card * (Y ∩ D).card := by
  classical
  rcases (Y ∩ D).eq_empty_or_nonempty with h_empty | h_nonempty
  · -- Y ∩ D = ∅: no σ has head in Y, both sides 0
    have h_filter : S.filter (fun σ =>
        ∃ x ∈ Y, (permDList σ D).head? = some x) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      rintro σ hσ
      simp only [Finset.mem_filter] at hσ
      obtain ⟨-, x, hxY, hhead⟩ := hσ
      have : x ∈ Y ∩ D :=
        Finset.mem_inter.mpr ⟨hxY, mem_of_permDList_head?_eq_some hhead⟩
      rw [h_empty] at this
      exact absurd this (Finset.notMem_empty x)
    rw [h_filter, Finset.card_empty, Nat.zero_mul, h_empty,
        Finset.card_empty, Nat.mul_zero]
  · -- Y ∩ D nonempty: decompose by head value
    have h_decomp : S.filter (fun σ =>
        ∃ x ∈ Y, (permDList σ D).head? = some x) =
        (Y ∩ D).biUnion (fun y => S.filter (fun σ =>
          (permDList σ D).head? = some y)) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · rintro ⟨hσS, x, hxY, hhead⟩
        exact ⟨x, ⟨hxY, mem_of_permDList_head?_eq_some hhead⟩, hσS, hhead⟩
      · rintro ⟨y, ⟨hyY, _⟩, hσS, hhead⟩
        exact ⟨hσS, y, hyY, hhead⟩
    have h_disjoint : (↑(Y ∩ D) : Set (Fin n)).PairwiseDisjoint
        (fun y => S.filter (fun σ => (permDList σ D).head? = some y)) := by
      intros y _ y' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      rintro σ ⟨_, h₁⟩ ⟨_, h₂⟩
      exact hne (Option.some.inj (h₁.symm.trans h₂))
    rw [h_decomp, Finset.card_biUnion h_disjoint, Finset.sum_mul,
        Finset.sum_congr rfl
          (fun y hy => card_filter_head_eq_mul y (Finset.mem_inter.mp hy).2 h_closed),
        Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Rational rate over a swap-closed family**: the fraction of `σ ∈ S` with
    `permDList`-head in `Y` is `|Y ∩ D| / |D|` (both as ℚ). For empty `D`,
    both sides are `0` by Lean's `0/0 = 0` convention. -/
theorem filter_head_in_rate_of_swaps (S : Finset (Equiv.Perm (Fin n)))
    (D Y : Finset (Fin n)) (h_S : S.Nonempty)
    (h_closed : ∀ y₁ ∈ D, ∀ y₂ ∈ D, ∀ σ ∈ S, Equiv.swap y₁ y₂ * σ ∈ S) :
    ((S.filter (fun σ => ∃ x ∈ Y, (permDList σ D).head? = some x)).card : ℚ) /
      (S.card : ℚ) =
    ((Y ∩ D).card : ℚ) / (D.card : ℚ) := by
  have h := filter_head_in_card_of_swaps S D Y h_closed
  have h_S_pos : 0 < S.card := h_S.card_pos
  rcases Nat.eq_zero_or_pos D.card with h_zero | h_pos
  · -- D empty: both sides reduce to 0
    have h_D_empty : D = ∅ := Finset.card_eq_zero.mp h_zero
    have hYD : (Y ∩ D).card = 0 := by simp [h_D_empty]
    have h_count_zero : (S.filter (fun σ =>
        ∃ x ∈ Y, (permDList σ D).head? = some x)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro σ hσ
      simp only [Finset.mem_filter] at hσ
      obtain ⟨-, x, -, hhead⟩ := hσ
      have hxD : x ∈ D := mem_of_permDList_head?_eq_some hhead
      rw [h_D_empty] at hxD
      exact (Finset.notMem_empty x) hxD
    rw [h_count_zero, hYD, h_zero, Nat.cast_zero, zero_div, zero_div]
  · -- D nonempty: clear denominators
    have h_d_ne : (D.card : ℚ) ≠ 0 := by
      simpa using Nat.pos_iff_ne_zero.mp h_pos
    have h_s_ne : (S.card : ℚ) ≠ 0 := by
      simpa using Nat.pos_iff_ne_zero.mp h_S_pos
    have h_cast : ((S.filter (fun σ =>
        ∃ x ∈ Y, (permDList σ D).head? = some x)).card : ℚ) * (D.card : ℚ) =
        (S.card : ℚ) * ((Y ∩ D).card : ℚ) := by
      exact_mod_cast h
    field_simp
    linarith [h_cast]

/-- **The closed-form count over all permutations**: `S = Finset.univ`
    specialization of `filter_head_in_card_of_swaps` (`|S| = n!`). -/
theorem perm_filter_head_in_card (D Y : Finset (Fin n)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ x ∈ Y, (permDList σ D).head? = some x)).card * D.card =
    n.factorial * (Y ∩ D).card := by
  have h := filter_head_in_card_of_swaps Finset.univ D Y
    (fun _ _ _ _ σ _ => Finset.mem_univ _)
  rwa [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h

/-- **Rational variation rate**: the fraction of permutations with
    `permDList`-head in `Y` is `|Y ∩ D| / |D|` (both as ℚ). `S = Finset.univ`
    specialization of `filter_head_in_rate_of_swaps`, intended for consumers
    stating per-context probabilities (e.g. `winProb … = 1/3`). -/
theorem perm_filter_head_in_rate (D Y : Finset (Fin n)) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ x ∈ Y, (permDList σ D).head? = some x)).card : ℚ) / n.factorial =
    ((Y ∩ D).card : ℚ) / D.card := by
  have h := filter_head_in_rate_of_swaps Finset.univ D Y Finset.univ_nonempty
    (fun _ _ _ _ σ _ => Finset.mem_univ _)
  rwa [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h

-- ============================================================================
-- § 7: List-filter head monotonicity under subset relations
-- ============================================================================

/-! Pure list-filter / `head?` facts about how `(L.filter (· ∈ D)).head?`
behaves under subset relations between `D` and `D'`. Used by factorial-typology
studies (e.g., `Studies/Zuraw2010.lean`'s structural
voicing/place implications) to propagate "first element of `L` falling in
`D` lies in `Y`" properties across distinguishing-set / favoring-set pairs.

Originally lived `private` inside `Zuraw2010.lean`; lifted here because they
are pure list/Finset facts with zero phonology content, and any cross-input
implication theorem in a binary-output OT factorial typology needs them. -/

variable {α : Type*} [DecidableEq α]

/-- Filtering `z :: zs` by `(· ∈ D)` when `z ∈ D` puts `z` first. -/
theorem filter_cons_head_of_mem (D : Finset α) (z : α) (zs : List α)
    (hzD : z ∈ D) :
    ((z :: zs).filter (· ∈ D)).head? = some z := by
  rw [List.head?_filter, List.find?_cons_of_pos (by simpa using hzD)]

/-- Filtering `z :: zs` by `(· ∈ D)` when `z ∉ D` recurses to `zs`. -/
theorem filter_cons_head_of_not_mem (D : Finset α) (z : α) (zs : List α)
    (hzD : z ∉ D) :
    ((z :: zs).filter (· ∈ D)).head? = (zs.filter (· ∈ D)).head? := by
  rw [List.head?_filter, List.head?_filter, List.find?_cons_of_neg (by simpa using hzD)]

/-- The head of a list filtered by a larger set `D ⊇ D'` still satisfies a
    "head-in-Y" property, provided `Y' ⊆ Y` and any element of the extra
    region `D \ D'` is in `Y` (so it counts as YES-favoring when it appears
    as the head of `L.filter (· ∈ D)`).

    Used for "voicing-style" implications in factorial typology: if `c'`
    has a smaller distinguishing set than `c` and `c`'s extras all favor
    YES, then `c' subbed ⇒ c subbed`. -/
theorem head_filter_subset_extends
    {D D' Y Y' : Finset α}
    (h_D : D' ⊆ D) (h_Y : Y' ⊆ Y)
    (h_extra : ∀ x ∈ D, x ∉ D' → x ∈ Y) :
    ∀ (L : List α),
      (∃ x ∈ Y', (L.filter (· ∈ D')).head? = some x) →
      (∃ y ∈ Y, (L.filter (· ∈ D)).head? = some y) := by
  intro L
  induction L with
  | nil =>
    rintro ⟨_, _, hx⟩; simp at hx
  | cons z zs ih =>
    rintro ⟨x, hxY', hx⟩
    by_cases hzD : z ∈ D
    · refine ⟨z, ?_, filter_cons_head_of_mem D z zs hzD⟩
      by_cases hzD' : z ∈ D'
      · -- z is the head of the D'-filter, so z = x ∈ Y' ⊆ Y
        rw [filter_cons_head_of_mem D' z zs hzD'] at hx
        rw [show z = x from Option.some.inj hx]
        exact h_Y hxY'
      · exact h_extra z hzD hzD'
    · -- z ∉ D ⊇ D', so z ∉ D': both filters skip z
      have hzD' : z ∉ D' := fun h => hzD (h_D h)
      rw [filter_cons_head_of_not_mem D' z zs hzD'] at hx
      obtain ⟨y, hyY, hy⟩ := ih ⟨x, hxY', hx⟩
      exact ⟨y, hyY, (filter_cons_head_of_not_mem D z zs hzD).trans hy⟩

/-- The head of a list filtered by a smaller set `D ⊆ D'` inherits a
    "head-in-Y" property from the larger filter, provided the YES-favorers
    `Y'` of the larger setting are entirely contained in the smaller `D`
    (so when the head of `L.filter (· ∈ D')` lies in `Y'`, it is also in
    `D`, hence the head of `L.filter (· ∈ D)`).

    Used for "place-style" implications in factorial typology: if `c'`
    has a larger distinguishing set than `c` but `c'`'s YES-favorers all
    lie in `c`'s smaller set, then `c' subbed ⇒ c subbed`. -/
theorem head_filter_smaller_inherits
    {D D' Y Y' : Finset α}
    (h_D : D ⊆ D') (h_Y : Y' ⊆ Y) (h_Y_in_D : Y' ⊆ D) :
    ∀ (L : List α),
      (∃ x ∈ Y', (L.filter (· ∈ D')).head? = some x) →
      (∃ y ∈ Y, (L.filter (· ∈ D)).head? = some y) := by
  intro L
  induction L with
  | nil =>
    rintro ⟨_, _, hx⟩; simp at hx
  | cons z zs ih =>
    rintro ⟨x, hxY', hx⟩
    by_cases hzD' : z ∈ D'
    · -- z is the head of the D'-filter, so z = x ∈ Y' ⊆ D
      rw [filter_cons_head_of_mem D' z zs hzD'] at hx
      rw [show z = x from Option.some.inj hx]
      have hxD : x ∈ D := h_Y_in_D hxY'
      exact ⟨x, h_Y hxY', filter_cons_head_of_mem D x zs hxD⟩
    · -- z ∉ D' ⊇ D, so z ∉ D: both filters skip z
      have hzD : z ∉ D := fun h => hzD' (h_D h)
      rw [filter_cons_head_of_not_mem D' z zs hzD'] at hx
      obtain ⟨y, hyY, hy⟩ := ih ⟨x, hxY', hx⟩
      exact ⟨y, hyY, (filter_cons_head_of_not_mem D z zs hzD).trans hy⟩

end Core.Optimization.PermSubsetCombinatorics

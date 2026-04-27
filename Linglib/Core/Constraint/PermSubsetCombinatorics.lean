import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Rat.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Permutation-Subset Combinatorics
@cite{anttila-1997} @cite{zuraw-2010}

A closed-form count of `Equiv.Perm (Fin n)` filtered by predicates
of the form "the highest-ranked constraint in `D` lies in `Y`" — the
canonical OT factorial-typology pattern.

## Main result

`perm_filter_head_in_card`: for `D Y : Finset (Fin n)`,

  `(# σ where head of permDList σ D ∈ Y) × |D| = n! × |Y ∩ D|`

This reduces O(n!) constraint-ranking enumeration to closed-form
arithmetic. Two factorial-typology studies consume it:
`Phenomena/Phonology/Studies/Zuraw2010.lean` and
`Phenomena/Phonology/Studies/Anttila1997.lean`.

## Proof technique

For each `y ∈ D`, the fiber `S_y = {σ : head of permDList σ D = y}`
is in bijection with any other fiber `S_y'` via left-multiplication
by `Equiv.swap y y'` (which preserves D-membership pointwise and
swaps the head element). All fibers thus have equal cardinality.
Summing over `D` (which partitions `Finset.univ` when `D` is nonempty)
gives `|D| × |S_y| = n!`, hence `|S_y| = n!/|D|`.

## Scope

Specialized to head-in-Y predicates on `Equiv.Perm (Fin n)`. A more
general factoring theorem for arbitrary D-determined predicates is
feasible (via orbit-stabilizer on the fixing subgroup of `Dᶜ`) but
currently has no consumer in the OT-variation literature.
-/

namespace Core.Constraint.PermSubsetCombinatorics

open Finset

variable {n : ℕ}

-- ============================================================================
-- § 1: permToList and permDList
-- ============================================================================

/-- The list `[σ 0, σ 1, …, σ (n-1)]` of σ's values in increasing index order. -/
def permToList (σ : Equiv.Perm (Fin n)) : List (Fin n) :=
  (List.finRange n).map σ

@[simp]
theorem permToList_length (σ : Equiv.Perm (Fin n)) :
    (permToList σ).length = n := by
  simp only [permToList, List.length_map, List.length_finRange]

theorem permToList_nodup (σ : Equiv.Perm (Fin n)) : (permToList σ).Nodup := by
  unfold permToList
  exact (List.nodup_finRange n).map σ.injective

@[simp]
theorem mem_permToList (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    x ∈ permToList σ := by
  simp only [permToList, List.mem_map, List.mem_finRange, true_and]
  exact ⟨σ.symm x, σ.apply_symm_apply x⟩

/-- Subsequence of `permToList σ` filtered to elements of `D`. The head
    of this list is the σ-image element that lies in D and has the
    smallest preimage index — i.e., the highest-ranked constraint in
    the OT interpretation. -/
def permDList (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) : List (Fin n) :=
  (permToList σ).filter (· ∈ D)

theorem permDList_nodup (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) :
    (permDList σ D).Nodup :=
  (permToList_nodup σ).filter _

@[simp]
theorem mem_permDList (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n))
    (x : Fin n) : x ∈ permDList σ D ↔ x ∈ D := by
  simp only [permDList, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
  intro _; exact mem_permToList σ x

@[simp]
theorem permDList_toFinset (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) :
    (permDList σ D).toFinset = D := by
  ext x
  rw [List.mem_toFinset, mem_permDList]

@[simp]
theorem permDList_length (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n)) :
    (permDList σ D).length = D.card := by
  rw [← List.toFinset_card_of_nodup (permDList_nodup σ D), permDList_toFinset]

/-- Decompose `permToList σ` at any position: the list factors as
    `(take k).map σ ++ σ k :: (drop (k+1)).map σ`. -/
theorem permToList_split_at (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    permToList σ =
    ((List.finRange n).take k.val).map σ ++ σ k ::
      ((List.finRange n).drop (k.val + 1)).map σ := by
  have h_lt : k.val < (List.finRange n).length := by
    rw [List.length_finRange]; exact k.isLt
  have h_get : (List.finRange n)[k.val]'h_lt = k := by simp [List.getElem_finRange]
  unfold permToList
  conv_lhs => rw [← List.take_append_drop k.val (List.finRange n)]
  rw [List.drop_eq_getElem_cons h_lt, h_get, List.map_append, List.map_cons]

/-- Inverse: if `permToList σ = pre ++ x :: suf`, then σ at the
    canonical Fin-position `pre.length` equals `x`. -/
theorem permToList_eq_append_cons_imp_apply (σ : Equiv.Perm (Fin n))
    (pre suf : List (Fin n)) (x : Fin n)
    (h_split : permToList σ = pre ++ x :: suf) (h_pre_lt : pre.length < n) :
    σ ⟨pre.length, h_pre_lt⟩ = x := by
  have h_split_pre := permToList_split_at σ ⟨pre.length, h_pre_lt⟩
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

/-- The head of `permDList σ D` characterized via mathlib's
    `List.find?_eq_some_iff_append`: `head = some x` iff `x ∈ D` and
    `permToList σ` decomposes as `prefix ++ x :: suffix` where every
    prefix element lies outside `D`. -/
theorem permDList_head_eq_some_iff (σ : Equiv.Perm (Fin n)) (D : Finset (Fin n))
    (x : Fin n) :
    (permDList σ D).head? = some x ↔
    x ∈ D ∧ ∃ pre suf : List (Fin n),
      permToList σ = pre ++ x :: suf ∧ ∀ y ∈ pre, y ∉ D := by
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

-- ============================================================================
-- § 2: Multiplicative lemma
-- ============================================================================

/-- `permToList` of a left-multiplied permutation: `(τ * σ).permToList`
    equals `σ.permToList` with τ applied element-wise. -/
theorem permToList_mul (τ σ : Equiv.Perm (Fin n)) :
    permToList (τ * σ) = (permToList σ).map τ := by
  unfold permToList
  rw [List.map_map]
  rfl

/-- When `τ` preserves D-membership both ways, the D-image of `τ * σ` is
    the D-image of `σ` with `τ` applied element-wise. -/
theorem permDList_mul_of_preserves_D
    (D : Finset (Fin n)) (σ τ : Equiv.Perm (Fin n))
    (h_pres : ∀ x : Fin n, x ∈ D ↔ τ x ∈ D) :
    permDList (τ * σ) D = (permDList σ D).map τ := by
  unfold permDList
  rw [permToList_mul]
  generalize permToList σ = l
  induction l with
  | nil => simp only [List.map_nil, List.filter_nil]
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases hx : x ∈ D
    · have hxD : τ x ∈ D := (h_pres x).mp hx
      simp only [hx, hxD, decide_true, List.map_cons, ih, ↓reduceIte]
    · have hxD : τ x ∉ D := fun h => hx ((h_pres x).mpr h)
      simp only [hx, hxD, decide_false, ih, Bool.false_eq_true, ↓reduceIte]

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

/-- If `(permDList σ D).head? = some x` then `x ∈ D` (since the head of
    a filtered list lies in the filter set) and `permDList σ D` is a
    cons. Used to dispatch cases when bridging head-equality hypotheses
    to membership facts. -/
private lemma head?_eq_some_imp_mem_D {D : Finset (Fin n)}
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

/-- For `y, y' ∈ D`, the fibers `{σ : head of permDList σ D = y}` and
    `{σ : head of permDList σ D = y'}` have equal cardinality, witnessed
    by the involution `σ ↦ Equiv.swap y y' * σ`. -/
private theorem card_filter_head_fibers_eq {D : Finset (Fin n)} (y y' : Fin n)
    (hy : y ∈ D) (hy' : y' ∈ D) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (permDList σ D).head? = some y)).card =
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (permDList σ D).head? = some y')).card := by
  apply Finset.card_bij (fun σ _ => Equiv.swap y y' * σ)
  · -- Maps into target fiber
    intros σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [permDList_mul_of_preserves_D D σ _ (swap_preserves_finset hy hy')]
    cases h_eq : permDList σ D with
    | nil => rw [h_eq] at hσ; exact absurd hσ (by simp)
    | cons z _ =>
      rw [h_eq] at hσ
      simp only [List.head?_cons, Option.some.injEq] at hσ
      subst hσ
      simp only [List.map_cons, List.head?_cons, Equiv.swap_apply_left]
  · -- Injective
    intros σ₁ _ σ₂ _ heq
    exact mul_left_cancel heq
  · -- Surjective
    intros σ' hσ'
    refine ⟨Equiv.swap y y' * σ', ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ' ⊢
      rw [permDList_mul_of_preserves_D D σ' _ (swap_preserves_finset hy hy')]
      cases h_eq : permDList σ' D with
      | nil => rw [h_eq] at hσ'; exact absurd hσ' (by simp)
      | cons z _ =>
        rw [h_eq] at hσ'
        simp only [List.head?_cons, Option.some.injEq] at hσ'
        subst hσ'
        simp only [List.map_cons, List.head?_cons, Equiv.swap_apply_right]
    · -- swap is an involution: swap * (swap * σ') = σ'
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

-- ============================================================================
-- § 5: Partition by head over a nonempty D
-- ============================================================================

/-- For nonempty `D`, the head of `permDList σ D` is always defined and
    lies in `D`. -/
private lemma head_in_D {D : Finset (Fin n)} (h_nonempty : D.Nonempty)
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
    exact head?_eq_some_imp_mem_D h_head

/-- For nonempty `D`, summing fiber cardinalities over `y ∈ D` gives `n!`,
    since every σ has its head in `D`. -/
private theorem sum_head_eq_card_eq_factorial {D : Finset (Fin n)}
    (h_nonempty : D.Nonempty) :
    ∑ y ∈ D, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (permDList σ D).head? = some y)).card = n.factorial := by
  classical
  have h_disjoint : (↑D : Set (Fin n)).PairwiseDisjoint
      (fun y => Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (permDList σ D).head? = some y)) := by
    intros y _ y' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro σ ⟨_, h₁⟩ ⟨_, h₂⟩
    exact hne (Option.some.inj (h₁.symm.trans h₂))
  have h_union : D.biUnion (fun y => Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (permDList σ D).head? = some y)) = Finset.univ := by
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => head_in_D h_nonempty σ⟩
  calc ∑ y ∈ D, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (permDList σ D).head? = some y)).card
      = (D.biUnion (fun y => Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (permDList σ D).head? = some y))).card :=
        (Finset.card_biUnion h_disjoint).symm
    _ = Finset.univ.card := by rw [h_union]
    _ = n.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- For `y ∈ D`, the count of perms whose `permDList σ D` starts with `y`
    is `n!/|D|`, expressed in multiplied form to avoid ℕ division. -/
private theorem head_eq_card {D : Finset (Fin n)} (y : Fin n) (hy : y ∈ D) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (permDList σ D).head? = some y)).card * D.card = n.factorial := by
  have h_nonempty : D.Nonempty := ⟨y, hy⟩
  have h_const : ∀ y' ∈ D,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (permDList σ D).head? = some y')).card =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (permDList σ D).head? = some y)).card :=
    fun y' hy' => card_filter_head_fibers_eq y' y hy' hy
  have h_sum := sum_head_eq_card_eq_factorial h_nonempty
  rw [Finset.sum_congr rfl h_const, Finset.sum_const, smul_eq_mul] at h_sum
  -- h_sum : D.card * (...).card = n.factorial; goal: (...).card * D.card = n.factorial
  rw [mul_comm]; exact h_sum

-- ============================================================================
-- § 6: Closed form for "head ∈ Y" predicates
-- ============================================================================

/-- **The closed-form count**: for the predicate "head of `permDList σ D`
    lies in `Y`", the number of permutations satisfying it is
    `n! × |Y ∩ D| / D.card`, expressed in multiplied form to avoid ℕ
    division.

    For each consonant in a factorial typology, this gives the per-consonant
    substitution count from a single application of the underlying head-fiber
    counting `head_eq_card` summed over `Y ∩ D`. -/
theorem perm_filter_head_in_card (D Y : Finset (Fin n)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ x ∈ Y, (permDList σ D).head? = some x)).card * D.card =
    n.factorial * (Y ∩ D).card := by
  classical
  rcases (Y ∩ D).eq_empty_or_nonempty with h_empty | h_nonempty
  · -- Y ∩ D = ∅: no σ has head in Y, both sides 0
    have h_filter : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        ∃ x ∈ Y, (permDList σ D).head? = some x) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      rintro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨x, hxY, hhead⟩ := hσ
      have : x ∈ Y ∩ D :=
        Finset.mem_inter.mpr ⟨hxY, head?_eq_some_imp_mem_D hhead⟩
      rw [h_empty] at this
      exact absurd this (Finset.notMem_empty x)
    rw [h_filter, Finset.card_empty, Nat.zero_mul, h_empty,
        Finset.card_empty, Nat.mul_zero]
  · -- Y ∩ D nonempty: decompose by head value
    have h_decomp : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        ∃ x ∈ Y, (permDList σ D).head? = some x) =
        (Y ∩ D).biUnion (fun y => Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (permDList σ D).head? = some y)) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hxY, hhead⟩
        exact ⟨x, ⟨hxY, head?_eq_some_imp_mem_D hhead⟩, hhead⟩
      · rintro ⟨y, ⟨hyY, _⟩, hhead⟩
        exact ⟨y, hyY, hhead⟩
    have h_disjoint : (↑(Y ∩ D) : Set (Fin n)).PairwiseDisjoint
        (fun y => Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (permDList σ D).head? = some y)) := by
      intros y _ y' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      rintro σ ⟨_, h₁⟩ ⟨_, h₂⟩
      exact hne (Option.some.inj (h₁.symm.trans h₂))
    rw [h_decomp, Finset.card_biUnion h_disjoint, Finset.sum_mul,
        Finset.sum_congr rfl
          (fun y hy => head_eq_card y (Finset.mem_inter.mp hy).2),
        Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Rational variation rate**: the fraction of permutations with
    `permDList`-head in `Y` is `|Y ∩ D| / |D|` (both as ℚ).

    Direct rational form of `perm_filter_head_in_card`, intended for
    consumers stating per-context probabilities (e.g.
    `pocPredict … = 1/3`). For empty `D`, both sides are `0/0 = 0` by
    Lean's convention. -/
theorem perm_filter_head_in_rate (D Y : Finset (Fin n)) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ x ∈ Y, (permDList σ D).head? = some x)).card : ℚ) / n.factorial =
    ((Y ∩ D).card : ℚ) / D.card := by
  have h := perm_filter_head_in_card D Y
  -- h : count * D.card = n.factorial * (Y ∩ D).card (in ℕ)
  have h_fact_pos : 0 < n.factorial := Nat.factorial_pos n
  rcases Nat.eq_zero_or_pos D.card with h_zero | h_pos
  · -- D empty: |Y ∩ D| = 0; both sides reduce to 0/...
    have hYD : (Y ∩ D).card = 0 := by
      rw [Finset.card_eq_zero] at h_zero
      simp [h_zero]
    have h_D_empty : D = ∅ := Finset.card_eq_zero.mp h_zero
    have h_count_zero : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        ∃ x ∈ Y, (permDList σ D).head? = some x)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨x, _, hhead⟩ := hσ
      have hxD : x ∈ D := head?_eq_some_imp_mem_D hhead
      rw [h_D_empty] at hxD
      exact (Finset.notMem_empty x) hxD
    rw [h_count_zero, hYD, h_zero, Nat.cast_zero, zero_div, zero_div]
  · -- D nonempty: derive rational form by clearing denominators
    have h_d_ne : (D.card : ℚ) ≠ 0 := by
      simpa using Nat.pos_iff_ne_zero.mp h_pos
    have h_fact_ne : (n.factorial : ℚ) ≠ 0 := by
      simpa using Nat.pos_iff_ne_zero.mp h_fact_pos
    have h_cast : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        ∃ x ∈ Y, (permDList σ D).head? = some x)).card : ℚ) *
        (D.card : ℚ) =
        (n.factorial : ℚ) * ((Y ∩ D).card : ℚ) := by
      exact_mod_cast h
    field_simp
    linarith [h_cast]

end Core.Constraint.PermSubsetCombinatorics

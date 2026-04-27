import Linglib.Core.Constraint.Cumulativity
import Linglib.Core.Constraint.PermSubsetCombinatorics

/-!
# Partially Ordered Constraints (POC)
@cite{anttila-1997} @cite{kiparsky-1993b} @cite{coetzee-pater-2011}

A POC grammar is a partial order on the constraint set. Each evaluation
samples a total order (i.e., a linear extension) consistent with the partial
order, and the OT optimum under that ranking is the output. The induced
distribution over outputs is uniform over consistent linear extensions.

This module provides the substrate counterpart to the per-paper POC
analyses: every linear extension is a `Equiv.Perm (Fin n)`, and every
finite set of consistent extensions sits inside `Finset.univ` for that
permutation type. The probability of an output is then a ratio of `Finset`
cardinalities — a clean computation, no measure theory required.

## Architecture

POC sits in the substrate alongside `Cumulativity.SystemicProblem`, sharing
its multi-input optimization model and its `OTRealizes` definition. The new
content here is:

- `PartialOrderConstraints n`: a partial order on `Fin n` (constraint indices).
- `IsConsistent p σ`: σ is a linear extension of p.
- `consistentTotalOrders p`: the (decidable, finite) set of linear extensions.
- `pocPredict P p i o`: the probability that POC sampling under p selects
  output o for input i, computed as a ratio of consistent extensions
  realizing o vs. all consistent extensions.
- `IsPOCRealizable P`: some non-trivial partial order has every consistent
  extension realizing the target. This is the categorical realizability
  notion; the probabilistic story is captured by `pocPredict`.

## Containments

- `poc_realizable_imp_ot_realizable` — trivial (pick any consistent extension).
- `ot_realizable_imp_poc_realizable` — non-trivial; the witness is the σ-induced
  total order, whose unique consistent extension is σ. The uniqueness step
  uses the standard fact that a strictly monotone bijection on a finite
  linear order is the identity (proof via `StrictMono.id_le` + dual).

The categorical containment `OT ⊆ POC` is somewhat misleading linguistically:
POC's expressive advantage over OT is *probabilistic*, not categorical. The
`pocPredict` API is the principled way to surface that — POC can produce
intermediate frequencies (e.g., 8/24, 12/24 in @cite{coetzee-pater-2011}'s
t/d-deletion analysis) that no single OT ranking can reproduce.

## Where this is used

`Phenomena/Phonology/Studies/CoetzeePater2011.lean` currently does its POC
analysis by manually enumerating `permutations constraints` and filtering.
A follow-up refactor would have CoetzeePater consume `pocPredict` and
substrate-level POC theorems instead.
-/

namespace Core.Constraint

open Finset

-- ============================================================================
-- § 1: Auxiliary — Strictly Monotone Bijection on Fin n is the Identity
-- ============================================================================

/-- A strictly monotone endo-function on `Fin n` is the identity. Both
    inequalities `id ≤ f` and `f ≤ id` follow from `StrictMono.id_le` (using
    `Fin n`'s `WellFoundedLT` instance) and its dual (using `WellFoundedGT`),
    which combine to `f = id` by antisymmetry. -/
private theorem fin_strictMono_eq_id {n : ℕ} (f : Fin n → Fin n)
    (hf : StrictMono f) : f = id := by
  funext k
  have h₁ : k ≤ f k := hf.id_le k
  have h₂ : f k ≤ k := hf.le_id k
  exact le_antisymm h₂ h₁

/-- A monotone bijection on `Fin n` is the identity. The bijection condition
    promotes monotone to strictly monotone (since equality of f-images forces
    equality of arguments), then `fin_strictMono_eq_id` finishes. -/
private theorem fin_monotone_bij_eq_id {n : ℕ}
    (f : Fin n → Fin n) (hbij : Function.Bijective f) (hmono : Monotone f) :
    f = id := by
  have hstrict : StrictMono f := by
    intro a b hab
    rcases lt_or_eq_of_le (hmono hab.le) with h | h
    · exact h
    · exact absurd (hbij.injective h) hab.ne
  exact fin_strictMono_eq_id f hstrict

-- ============================================================================
-- § 2: PartialOrderConstraints
-- ============================================================================

/-- A partial order on `Fin n` constraint indices. The OT case is a total
    order; the POC case allows incomparable pairs (multiple consistent
    linear extensions). -/
structure PartialOrderConstraints (n : ℕ) where
  /-- The partial-order relation: `rel a b` reads "a is ranked at-most-as-low-as
      b", i.e., a takes priority over b (or they're equal). -/
  rel : Fin n → Fin n → Prop
  /-- Decidability of the relation (required for `consistentTotalOrders` to
      be a computable `Finset`). -/
  decidable_rel : DecidableRel rel
  /-- Reflexivity. -/
  refl : ∀ a, rel a a
  /-- Transitivity. -/
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  /-- Antisymmetry. -/
  antisymm : ∀ {a b}, rel a b → rel b a → a = b

attribute [instance] PartialOrderConstraints.decidable_rel

namespace PartialOrderConstraints

variable {n : ℕ}

/-- The discrete partial order on `Fin n`: `rel a b` iff `a = b`. No
    constraint pair is comparable beyond reflexivity. Every permutation
    is a consistent linear extension — this matches @cite{anttila-1997}'s
    "no ranking imposed" baseline. -/
def discrete (n : ℕ) : PartialOrderConstraints n where
  rel := Eq
  decidable_rel := inferInstance
  refl := fun _ => rfl
  trans := Eq.trans
  antisymm := fun h _ => h

/-- The total order induced by a permutation `σ`: `rel a b` iff
    `σ.symm a ≤ σ.symm b` (i.e., a appears at least as early as b in σ's
    enumeration). This is a total order; its unique consistent linear
    extension is σ itself (`fromPermutation_consistent_unique` below). -/
def fromPermutation (σ : Equiv.Perm (Fin n)) : PartialOrderConstraints n where
  rel := fun a b => σ.symm a ≤ σ.symm b
  decidable_rel := fun _ _ => inferInstance
  refl := fun _ => le_refl _
  trans := fun h₁ h₂ => le_trans h₁ h₂
  antisymm := fun h₁ h₂ => σ.symm.injective (le_antisymm h₁ h₂)

/-- A permutation σ is **consistent** with the partial order p if σ⁻¹
    respects rel: whenever `rel a b` holds, σ ranks a at least as early
    as b (`σ.symm a ≤ σ.symm b`). σ is a linear extension of p. -/
def IsConsistent (p : PartialOrderConstraints n) (σ : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ a b, p.rel a b → σ.symm a ≤ σ.symm b

instance (p : PartialOrderConstraints n) (σ : Equiv.Perm (Fin n)) :
    Decidable (p.IsConsistent σ) := by
  unfold IsConsistent; infer_instance

/-- The (decidable, finite) set of linear extensions of `p`. -/
def consistentTotalOrders (p : PartialOrderConstraints n) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter p.IsConsistent

@[simp]
theorem mem_consistentTotalOrders {p : PartialOrderConstraints n}
    {σ : Equiv.Perm (Fin n)} :
    σ ∈ p.consistentTotalOrders ↔ p.IsConsistent σ := by
  simp [consistentTotalOrders]

/-- For the discrete partial order, every permutation is a linear extension. -/
theorem consistentTotalOrders_discrete (n : ℕ) :
    (discrete n).consistentTotalOrders = Finset.univ := by
  ext σ
  simp [consistentTotalOrders, IsConsistent, discrete]

/-- σ is consistent with the partial order it induces. -/
theorem isConsistent_fromPermutation (σ : Equiv.Perm (Fin n)) :
    (fromPermutation σ).IsConsistent σ := by
  intro a b h
  exact h

/-- The σ-induced total order has σ as a consistent linear extension. -/
theorem mem_consistentTotalOrders_fromPermutation (σ : Equiv.Perm (Fin n)) :
    σ ∈ (fromPermutation σ).consistentTotalOrders :=
  mem_consistentTotalOrders.mpr (isConsistent_fromPermutation σ)

/-- **Uniqueness**: the σ-induced total order has σ as its *unique*
    consistent linear extension. Any consistent τ must agree with σ
    pointwise (since τ.symm ∘ σ is a monotone bijection on `Fin n`, hence
    the identity by `fin_monotone_bij_eq_id`). -/
theorem fromPermutation_consistent_unique {σ τ : Equiv.Perm (Fin n)}
    (hτ : (fromPermutation σ).IsConsistent τ) : τ = σ := by
  have hcomp : ⇑τ.symm ∘ ⇑σ = id := by
    apply fin_monotone_bij_eq_id
    · exact τ.symm.bijective.comp σ.bijective
    · intro a b hab
      have hrel : (fromPermutation σ).rel (σ a) (σ b) := by
        show σ.symm (σ a) ≤ σ.symm (σ b)
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hab
      exact hτ (σ a) (σ b) hrel
  apply Equiv.ext
  intro k
  have hk : τ.symm (σ k) = k := congr_fun hcomp k
  calc τ k = τ (τ.symm (σ k)) := by rw [hk]
    _ = σ k := τ.apply_symm_apply (σ k)

@[simp]
theorem consistentTotalOrders_fromPermutation (σ : Equiv.Perm (Fin n)) :
    (fromPermutation σ).consistentTotalOrders = {σ} := by
  ext τ
  rw [mem_consistentTotalOrders, Finset.mem_singleton]
  refine ⟨fromPermutation_consistent_unique, fun hτ => ?_⟩
  rw [hτ]
  exact isConsistent_fromPermutation σ

theorem consistentTotalOrders_nonempty_of_fromPermutation
    (σ : Equiv.Perm (Fin n)) :
    (fromPermutation σ).consistentTotalOrders.Nonempty :=
  ⟨σ, mem_consistentTotalOrders_fromPermutation σ⟩

end PartialOrderConstraints

-- ============================================================================
-- § 3: POC Realizability of SystemicProblem
-- ============================================================================

namespace SystemicProblem

variable {Input Output : Type*} {n : ℕ}

/-- A partial order p **POC-realizes** the target if it has at least one
    consistent extension and every consistent extension realizes the target.
    This is the *categorical* realizability notion: target probability = 1
    under POC sampling. -/
def POCRealizes (P : SystemicProblem Input Output n)
    (p : PartialOrderConstraints n) : Prop :=
  p.consistentTotalOrders.Nonempty ∧
  ∀ σ ∈ p.consistentTotalOrders, P.OTRealizes σ

/-- A `SystemicProblem` is **POC-realizable** if some partial order
    categorically realizes the target. -/
def IsPOCRealizable (P : SystemicProblem Input Output n) : Prop :=
  ∃ p : PartialOrderConstraints n, P.POCRealizes p

end SystemicProblem

-- ============================================================================
-- § 4: Containments — OT ⊆ POC, POC ⊆ OT (categorical)
-- ============================================================================

/-- **Trivial direction**: every POC-realized target is OT-realized
    (pick any single consistent extension). -/
theorem poc_realizable_imp_ot_realizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsPOCRealizable → P.IsOTRealizable := by
  rintro ⟨p, hne, hreal⟩
  obtain ⟨σ, hσ⟩ := hne
  exact ⟨σ, hreal σ hσ⟩

/-- **Non-trivial direction**: every OT-realized target is POC-realized
    (the witness is the σ-induced total order, whose unique consistent
    extension is σ itself by `fromPermutation_consistent_unique`). -/
theorem ot_realizable_imp_poc_realizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsOTRealizable → P.IsPOCRealizable := by
  rintro ⟨σ, hσ⟩
  refine ⟨PartialOrderConstraints.fromPermutation σ, ?_, ?_⟩
  · exact PartialOrderConstraints.consistentTotalOrders_nonempty_of_fromPermutation σ
  · intro τ hτ
    rw [PartialOrderConstraints.consistentTotalOrders_fromPermutation,
        Finset.mem_singleton] at hτ
    rw [hτ]
    exact hσ

/-- **Categorical equivalence**: under categorical realizability,
    OT-realizable and POC-realizable coincide. POC's *probabilistic*
    advantage over OT is captured separately by `pocPredict` (next section);
    no categorical theorem distinguishes them. -/
theorem isOTRealizable_iff_isPOCRealizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) :
    P.IsOTRealizable ↔ P.IsPOCRealizable :=
  ⟨ot_realizable_imp_poc_realizable P,
   poc_realizable_imp_ot_realizable P⟩

-- ============================================================================
-- § 5: Probabilistic POC — pocPredict
-- ============================================================================

namespace PartialOrderConstraints

variable {Input Output : Type*} [DecidableEq Output] {n : ℕ}

/-- σ **picks** output o for input i if o is the unique strict OT winner
    (every other in-set candidate is lex-strictly worse than o under σ).

    Bare-args version: takes `cands` and `vp` directly rather than bundled
    in a `SystemicProblem`. POC analyses don't need a target — they're about
    distribution over outputs, not realization of a chosen one. -/
def PicksAt (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Input) (o : Output) : Prop :=
  o ∈ cands i ∧
  ∀ o' ∈ cands i, o' ≠ o →
    LexStrictlyBetter
      (fun k : Fin n => vp i o (σ k))
      (fun k : Fin n => vp i o' (σ k))

instance (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Input) (o : Output) :
    Decidable (PicksAt cands vp σ i o) := by
  unfold PicksAt; infer_instance

/-- The probability that POC sampling under partial order p selects output
    o for input i: ratio of consistent extensions picking o to total
    consistent extensions. Uses ℚ's `0/0 = 0` convention to handle the
    degenerate empty-consistent-set case without an explicit guard. -/
def pocPredict (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (p : PartialOrderConstraints n) (i : Input) (o : Output) : ℚ :=
  ((p.consistentTotalOrders.filter
    (fun σ => PicksAt cands vp σ i o)).card : ℚ) /
  (p.consistentTotalOrders.card : ℚ)

/-- For the σ-induced total order, `pocPredict` collapses to a δ at σ's
    OT-pick: probability 1 if σ picks o, probability 0 otherwise. -/
theorem pocPredict_fromPermutation
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Input) (o : Output) :
    pocPredict cands vp (fromPermutation σ) i o =
    if PicksAt cands vp σ i o then 1 else 0 := by
  simp only [pocPredict,
    consistentTotalOrders_fromPermutation,
    Finset.card_singleton, Nat.cast_one, div_one, Finset.filter_singleton]
  by_cases h : PicksAt cands vp σ i o
  · simp [if_pos h]
  · simp [if_neg h]

/-- Discrete-PO predict: uniform over all permutations (no ranking imposed).
    Counts the σ's that pick o, divides by `n!`. -/
theorem pocPredict_discrete
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (o : Output) :
    pocPredict cands vp (discrete n) i o =
    ((Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => PicksAt cands vp σ i o)).card : ℚ) /
    (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
  simp only [pocPredict, consistentTotalOrders_discrete]

end PartialOrderConstraints

-- ============================================================================
-- § 6: Bridge — PicksAt for binary candidates ↔ head-in-Y on permDList
-- ============================================================================

/-! For binary candidate sets `cands i = {chosen, other}`, `PicksAt σ i chosen`
reduces to `LexStrictlyBetter (vp i chosen ∘ σ) (vp i other ∘ σ)` (the
∀-quantifier collapses to a single check). And that lex predicate is exactly
"the highest-ranked constraint in the distinguishing set `D` favors `chosen`"
— i.e., `head of permDList σ D ∈ Y` where `D = {k : vp chosen k ≠ vp other k}`
and `Y = {k : vp chosen k < vp other k}`.

This bridges POC's lex-strict-better predicate to
`Core.Constraint.PermSubsetCombinatorics.perm_filter_head_in_card`'s closed
form, letting any binary-candidate POC study compute its `pocPredict` value
in closed form (`n! × |Y ∩ D| / |D|`) without enumerating `n!` rankings.

Used by `Phenomena/Phonology/Studies/CoetzeePater2011.lean` (English t/d-deletion;
binary `{retain, delete}` outputs across 3 contexts). -/

namespace PartialOrderConstraints

open Core.Constraint.PermSubsetCombinatorics

variable {Input : Type*} {n : ℕ}

/-- For binary candidate sets, `PicksAt σ i chosen` is equivalent to
    "the head of `permDList σ D` lies in `Y`", where `D` is the set of
    constraints distinguishing `chosen` from `other` and `Y` is the
    favoring subset (`vp chosen < vp other`).

    The bridge uses `permDList_head_eq_some_iff` + `permToList_split_at` +
    `permToList_eq_append_cons_imp_apply` (substrate) to translate
    between LexStrictlyBetter's `∃k` form and the head-in-Y characterization. -/
theorem picksAt_binary_iff_permDList_head_lt {Output : Type*} [DecidableEq Output]
    (cands : Input → Finset Output) (vp : Input → Output → Fin n → ℕ)
    (i : Input) (chosen other : Output)
    (h_two : cands i = {chosen, other}) (h_ne : chosen ≠ other)
    (σ : Equiv.Perm (Fin n)) :
    PicksAt cands vp σ i chosen ↔
    ∃ x ∈ Finset.univ.filter (fun k : Fin n => vp i chosen k < vp i other k),
      (permDList σ (Finset.univ.filter
        (fun k : Fin n => vp i chosen k ≠ vp i other k))).head? = some x := by
  classical
  -- Step 1: PicksAt with binary cands reduces to LexStrictlyBetter on chosen vs other
  have h_picksAt_iff_lex :
      PicksAt cands vp σ i chosen ↔
      Core.Constraint.LexStrictlyBetter
        (fun k => vp i chosen (σ k)) (fun k => vp i other (σ k)) := by
    unfold PicksAt
    constructor
    · rintro ⟨_, h_lex⟩
      exact h_lex other (by rw [h_two]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
        (Ne.symm h_ne)
    · intro h_lex
      refine ⟨by rw [h_two]; exact Finset.mem_insert_self _ _, ?_⟩
      intro o' h_o' h_o'_ne
      -- o' ∈ {chosen, other} ∧ o' ≠ chosen → o' = other
      rw [h_two, Finset.mem_insert, Finset.mem_singleton] at h_o'
      rcases h_o' with h | h
      · exact absurd h h_o'_ne
      · subst h; exact h_lex
  rw [h_picksAt_iff_lex]
  -- Step 2: LexStrictlyBetter ↔ head-in-Y characterization
  set D := Finset.univ.filter (fun k : Fin n => vp i chosen k ≠ vp i other k) with hD_def
  set Y := Finset.univ.filter (fun k : Fin n => vp i chosen k < vp i other k) with hY_def
  have h_D_iff : ∀ k, k ∈ D ↔ vp i chosen k ≠ vp i other k := by
    intro k; simp [hD_def]
  have h_Y_iff : ∀ k, k ∈ Y ↔ vp i chosen k < vp i other k := by
    intro k; simp [hY_def]
  constructor
  · -- LexStrictlyBetter → head-in-Y
    rintro ⟨k, h_below, h_lt⟩
    have h_σk_Y : σ k ∈ Y := (h_Y_iff (σ k)).mpr h_lt
    have h_σk_D : σ k ∈ D := (h_D_iff (σ k)).mpr (Nat.ne_of_lt h_lt)
    have h_below_notD : ∀ j < k, σ j ∉ D := fun j hj h =>
      ((h_D_iff (σ j)).mp h) (h_below j hj)
    refine ⟨σ k, h_σk_Y, ?_⟩
    rw [permDList_head_eq_some_iff]
    refine ⟨h_σk_D, ((List.finRange n).take k.val).map σ,
            ((List.finRange n).drop (k.val + 1)).map σ, permToList_split_at σ k, ?_⟩
    intro y hy
    obtain ⟨j, h_j_take, h_σj⟩ := List.mem_map.mp hy
    rw [List.mem_take_iff_getElem] at h_j_take
    obtain ⟨idx, h_idx_lt, h_idx_eq⟩ := h_j_take
    simp only [List.getElem_finRange] at h_idx_eq
    have h_idx_lt_k : idx < k.val := by
      simp only [List.length_finRange] at h_idx_lt
      omega
    have h_j_lt_k : j < k := by
      rw [Fin.lt_def, ← h_idx_eq]; exact h_idx_lt_k
    rw [← h_σj]
    exact h_below_notD j h_j_lt_k
  · -- head-in-Y → LexStrictlyBetter
    rintro ⟨x, hx_Y, h_head⟩
    rw [permDList_head_eq_some_iff] at h_head
    obtain ⟨h_x_D, pre, suf, h_split, h_pre⟩ := h_head
    have h_pre_len_lt : pre.length < n := by
      have h_perm_len : (permToList σ).length = n := permToList_length σ
      rw [h_split] at h_perm_len
      simp [List.length_append, List.length_cons] at h_perm_len
      omega
    have h_σk_x := permToList_eq_append_cons_imp_apply σ pre suf x h_split h_pre_len_lt
    refine ⟨⟨pre.length, h_pre_len_lt⟩, ?_, ?_⟩
    · -- ∀ j < ⟨pre.length, _⟩, vp chosen (σ j) = vp other (σ j)
      intro j h_j_lt
      rw [Fin.lt_def] at h_j_lt
      -- σ j is the j-th element of `((finRange n).take pre.length).map σ` (= pre)
      have h_split_pre := permToList_split_at σ ⟨pre.length, h_pre_len_lt⟩
      -- Combined: ((take pre.length).map σ) ++ σ ⟨...⟩ :: ((drop _).map σ) = pre ++ x :: suf
      have h_lhs_pre_len : (((List.finRange n).take pre.length).map σ).length = pre.length := by
        rw [List.length_map, List.length_take, List.length_finRange]; omega
      have h_combined : ((List.finRange n).take pre.length).map σ ++
          σ ⟨pre.length, h_pre_len_lt⟩ ::
          ((List.finRange n).drop (pre.length + 1)).map σ = pre ++ x :: suf := by
        rw [← h_split_pre]; exact h_split
      have h_pre_eq : ((List.finRange n).take pre.length).map σ = pre :=
        (List.append_inj h_combined h_lhs_pre_len).1
      -- σ j ∈ pre (j-th element of pre is σ j)
      have h_σj_in_pre : σ j ∈ pre := by
        rw [← h_pre_eq]
        refine List.mem_map.mpr ⟨j, ?_, rfl⟩
        rw [List.mem_take_iff_getElem]
        refine ⟨j.val, ?_, by simp [List.getElem_finRange]⟩
        simp only [List.length_finRange, lt_min_iff]
        exact ⟨h_j_lt, j.isLt⟩
      have h_eq : ¬ vp i chosen (σ j) ≠ vp i other (σ j) := fun h =>
        (h_pre _ h_σj_in_pre) ((h_D_iff (σ j)).mpr h)
      exact not_not.mp h_eq
    · show vp i chosen (σ ⟨pre.length, h_pre_len_lt⟩) <
          vp i other (σ ⟨pre.length, h_pre_len_lt⟩)
      rw [h_σk_x]
      exact (h_Y_iff x).mp hx_Y

end PartialOrderConstraints

end Core.Constraint

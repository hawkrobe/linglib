import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
import Linglib.Core.Combinatorics.Antimatroid
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# OT — the ERC–Antimatroid isomorphism

[merchant-riggle-2016] prove that consistent ERC sets over `n` constraints are
isomorphic to antimatroids on `Fin n`. This file builds that correspondence on top
of the framework-agnostic antimatroid theory in
`Linglib.Core.Combinatorics.Antimatroid` (`SetSystem`, `Antimatroid`,
`Antimatroid.free`/`trace`/`RootedCircuit`). The two maps `Antimat` (ERCs →
antimatroids) and `RCErc` (antimatroids → ERCs) are mutually inverse homomorphisms
preserving entailment/containment, so any antimatroid result transfers to OT.

## ERC → Antimatroid pipeline

- `MChain` — maps a consistent ERC set to its feasible sets (Definition 1)
- `Antimat` — maps a consistent ERC set to an antimatroid (Definition 6)
- `RCErc` — maps an antimatroid to an ERC set (Definition 10)

## Decidable feasibility and the simple-ERC fragment

- `Feasible` — the decidable, `Finset`-valued *local* feasibility condition; a
  sound over-approximation of the antimatroid family
- `FeasiblePrefix` — the faithful, also-decidable family (`MChain` over `Finset`)
- `feasible_not_accessible` — for general (disjunctive) ERCs `Feasible` strictly
  over-approximates and is not even accessible
- `feasible_iff_feasiblePrefix_of_simple` — on the simple-ERC fragment the two
  coincide (Birkhoff order-ideal ↔ linear-extension-prefix correspondence)
- `Antimat.ofSimple` — the resulting decidable antimatroid on a simple ERC set

## Lemmas and theorems

- `maximalChain_dominance` — prefix sets are downward-closed under dominance
- `MChain.union_closed` — Lemma 3: MChain is union-closed
- `Antimat_entailment` — Theorem 3: entailment → containment (proved)
- `RCErc_single_eq_simpleERC` — two-element rooted circuits are simple ERCs (proved)
- `Antimat_RCErc_inv` — Theorem 1: `Antimat ∘ RCErc = id` (stated; proof `sorry`)
- `RCErc_Antimat_inv` — Theorem 2: `RCErc ∘ Antimat = id` up to entailment
  (stated; proof `sorry`)
- `RCErc_entailment` — Theorem 4: containment → entailment (stated; proof `sorry`)

The three `sorry`s are the general antimatroid → ERC direction, which rests on
[dietrich-1987]'s rooted-circuit characterization of feasible sets.

## References

[dietrich-1987] — A circuit set characterization of antimatroids
[merchant-riggle-2016] — OT grammars, beyond partial orders:
ERC sets and antimatroids
-/

namespace OptimalityTheory
open Constraints

-- ============================================================================
-- § 9: Maximal Chains (Definition 1)
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
-- § 10: MChain — ERC Set → Feasible Sets
-- ============================================================================

/-- `MChain E` is the collection of subsets of `Fin n` that appear in
    some maximal chain consistent with ERC set `E`.

    A set `S` is in `MChain(E)` iff there exists a ranking `r` that
    satisfies all ERCs in `E` and a position `k` such that `S` is the
    set of the top-`k` constraints under `r`.

    [merchant-riggle-2016] Definition 1. -/
def MChain {n : Nat} (E : List (ERC n)) : Set (Fin n) → Prop :=
  fun S => ∃ r : Ranking n, ERCSet.SatisfiedBy r E ∧
    ∃ k : Fin (n + 1), maximalChain r k = S

/-! ### Local feasibility — a decidable sound over-approximation -/

/-- **Local feasibility** of a candidate prefix `S` against ERC set `E`: for
every ERC, if `S` contains one of its losers then it contains one of its winners
(one rooted circuit per loser). Decidable and `decide`-reducing.

`Feasible` is a *necessary* condition for antimatroid feasibility — implied by
`FeasiblePrefix`/`MChain` (`feasible_of_satisfiedBy`) — but **strictly weaker for
disjunctive (multi-`W`) ERCs**: two ERCs can mutually cover each other's losers
inside `S` with no consistent global order realizing it
(`feasible_not_accessible`). It is **exact** only on the simple-ERC fragment
(each ERC one `W`/one `L` = a Hasse edge = a partial order,
`feasible_iff_feasiblePrefix_of_simple`). The faithful, *also decidable* notion
is `FeasiblePrefix`. -/
def Feasible {n : Nat} (E : List (ERC n)) (S : Finset (Fin n)) : Prop :=
  ∀ α ∈ E, (∃ l, α l = .L ∧ l ∈ S) → (∃ w, α w = .W ∧ w ∈ S)

instance {n : Nat} (E : List (ERC n)) : DecidablePred (Feasible E) :=
  fun S => by unfold Feasible; infer_instance

/-- The empty prefix is locally feasible (no losers present). -/
@[simp] theorem Feasible.empty {n : Nat} (E : List (ERC n)) :
    Feasible E (∅ : Finset (Fin n)) := by
  intro α _ ⟨l, _, hl⟩; exact absurd hl (Finset.notMem_empty l)

/-- **Local feasibility is union-closed** (a one-liner): a loser in `S ∪ T` lies
in one of them, whose winner then lies in `S ∪ T`. (This is union-closure of the
over-approximation; the faithful family's union-closure is `MChain.union_closed`,
[merchant-riggle-2016] Lemma 3.) -/
theorem Feasible.union_closed {n : Nat} (E : List (ERC n)) {S T : Finset (Fin n)}
    (hS : Feasible E S) (hT : Feasible E T) : Feasible E (S ∪ T) := by
  intro α hα ⟨l, hlL, hlST⟩
  rcases Finset.mem_union.mp hlST with hlS | hlT
  · obtain ⟨w, hwW, hwS⟩ := hS α hα ⟨l, hlL, hlS⟩
    exact ⟨w, hwW, Finset.mem_union.mpr (Or.inl hwS)⟩
  · obtain ⟨w, hwW, hwT⟩ := hT α hα ⟨l, hlL, hlT⟩
    exact ⟨w, hwW, Finset.mem_union.mpr (Or.inr hwT)⟩

/-- The top-`k` constraints under ranking `r`, as a `Finset` (the decidable
counterpart of `maximalChain r k`). -/
def prefixFinset {n : Nat} (r : Ranking n) (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (r.symm i : Nat) < k.val)

@[simp] theorem mem_prefixFinset {n : Nat} (r : Ranking n) (k : Fin (n + 1)) (i : Fin n) :
    i ∈ prefixFinset r k ↔ (r.symm i : Nat) < k.val := by simp [prefixFinset]

/-- **Forward representation** (the easy half of [merchant-riggle-2016]'s
isomorphism): a prefix of a ranking that satisfies `E` is locally feasible.
Winners dominate their losers, so a loser inside the prefix drags its winner in
(`maximalChain_dominance` in `Finset` form). -/
theorem feasible_of_satisfiedBy {n : Nat} {E : List (ERC n)} {r : Ranking n}
    (hr : ERCSet.SatisfiedBy r E) (k : Fin (n + 1)) : Feasible E (prefixFinset r k) := by
  intro α hα ⟨l, hlL, hlmem⟩
  rw [mem_prefixFinset] at hlmem
  obtain ⟨w, hwW, hdom⟩ := (ERC.satisfiedBy_iff_dominance r α).mp (hr α hα) l hlL
  exact ⟨w, hwW, by rw [mem_prefixFinset]; unfold Ranking.Dominates at hdom; omega⟩

/-! ### `FeasiblePrefix` — the faithful, decidable antimatroid feasibility -/

/-- **Faithful feasibility**: `S` is the top-`k` constraints of *some* ranking
satisfying `E` — the `Finset`-valued form of `MChain`. Decidable by finite search
over `Ranking n` (a `Fintype`) and `Fin (n+1)`, so `decide` reduces — *and*
unlike `Feasible` it is the genuine antimatroid family, not an over-approximation. -/
def FeasiblePrefix {n : Nat} (E : List (ERC n)) (S : Finset (Fin n)) : Prop :=
  ∃ r : Ranking n, ERCSet.SatisfiedBy r E ∧ ∃ k : Fin (n + 1), prefixFinset r k = S

instance {n : Nat} (E : List (ERC n)) : DecidablePred (FeasiblePrefix E) :=
  fun _ => Fintype.decidableExistsFintype

/-- The faithful predicate implies the over-approximation (`feasible_of_satisfiedBy`). -/
theorem feasible_of_feasiblePrefix {n : Nat} {E : List (ERC n)} {S : Finset (Fin n)}
    (h : FeasiblePrefix E S) : Feasible E S := by
  obtain ⟨r, hr, k, rfl⟩ := h; exact feasible_of_satisfiedBy hr k

/-- `prefixFinset` coerces to `maximalChain`. -/
@[simp] theorem prefixFinset_coe {n : Nat} (r : Ranking n) (k : Fin (n + 1)) :
    (↑(prefixFinset r k) : Set (Fin n)) = maximalChain r k := by
  ext i; simp [prefixFinset, maximalChain]

/-- `FeasiblePrefix` is `MChain` over `Finset` — the decidable counterpart of the
existential, `Set`-valued antimatroid family. -/
theorem mChain_coe_iff_feasiblePrefix {n : Nat} (E : List (ERC n)) (S : Finset (Fin n)) :
    MChain E (↑S) ↔ FeasiblePrefix E S := by
  constructor
  · rintro ⟨r, hr, k, hk⟩
    exact ⟨r, hr, k, Finset.coe_inj.mp ((prefixFinset_coe r k).trans hk)⟩
  · rintro ⟨r, hr, k, rfl⟩; exact ⟨r, hr, k, (prefixFinset_coe r k).symm⟩

/-- **`Feasible` strictly over-approximates the antimatroid family.** Two
disjunctive (multi-`W`) ERCs over `Fin 4` admit a locally-feasible `{0,1}` that
is *not* a prefix of any consistent ranking (`¬ FeasiblePrefix`) and has *no*
removable element — so `{S | Feasible E S}` is not accessible and cannot be an
antimatroid for general ERC sets. Hence `Antimat.IsFeasible` stays `MChain`
([merchant-riggle-2016]'s "beyond partial orders"); the local form is exact only
on the simple-ERC fragment. -/
theorem feasible_not_accessible :
    ∃ (E : List (ERC 4)) (S : Finset (Fin 4)),
      ERCSet.Consistent E ∧ Feasible E S ∧ ¬ FeasiblePrefix E S ∧
        S.Nonempty ∧ ¬ ∃ x ∈ S, Feasible E (S \ {x}) :=
  ⟨[fun i => if i = 0 then .W else if i = 1 then .L else if i = 2 then .W else .e,
    fun i => if i = 0 then .L else if i = 1 then .W else if i = 2 then .e else .W],
   {0, 1}, by decide, by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- § 11: Union Closure (Lemma 3)
-- ============================================================================

/-- Prefix sets are downward-closed under dominance: if `w` dominates
    `l` under ranking `r` and `l` is in the prefix set at position `k`,
    then `w` is too (since `r.symm w < r.symm l < k`).

    This is the key insight enabling the direct construction proof of
    union closure: any W-witness for an L-constraint in a prefix set
    must itself be in that prefix set. -/
theorem maximalChain_dominance {n : Nat} (r : Ranking n) (k : Fin (n + 1))
    (w l : Fin n) (hw : r.Dominates w l) (hl : l ∈ maximalChain r k) :
    w ∈ maximalChain r k := by
  simp only [maximalChain, Set.mem_setOf_eq] at hl ⊢
  unfold Ranking.Dominates at hw; omega

-- Helpers for the union closure construction

/-- Count elements in finset `s` ranked strictly below `i` by `r`. -/
private def countBelow {n : Nat} (r : Ranking n)
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
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hj, Equiv.symm_apply_apply]
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

    [merchant-riggle-2016] Lemma 3. -/
theorem MChain.union_closed {n : Nat} (E : List (ERC n))
    (_hcons : ERCSet.Consistent E) (S T : Set (Fin n))
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
  -- r₃.dominates w l ↔ f w < f l
  have hdom : ∀ w l, r₃.Dominates w l ↔ f w < f l := by
    intro w l; unfold Ranking.Dominates; constructor
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
  have hsat : ERCSet.SatisfiedBy r₃ E := by
    intro α hα
    rw [ERC.satisfiedBy_iff_dominance]
    intro l hl_L
    by_cases h1 : inS l
    · -- l ∈ S: use r₁
      obtain ⟨w, hw_W, hw_dom⟩ := (ERC.satisfiedBy_iff_dominance r₁ α).mp (hr₁ α hα) l hl_L
      have hw_S : inS w := by
        have := maximalChain_dominance r₁ k₁ w l hw_dom
          (show l ∈ maximalChain r₁ k₁ by simp [maximalChain]; exact h1)
        simp [maximalChain] at this; exact this
      exact ⟨w, hw_W, (hdom w l).mpr (by simp only [f, if_pos hw_S, if_pos h1]; exact hw_dom)⟩
    · by_cases h2 : inT l
      · -- l ∈ T\S: use r₂
        obtain ⟨w, hw_W, hw_dom⟩ := (ERC.satisfiedBy_iff_dominance r₂ α).mp (hr₂ α hα) l hl_L
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
        obtain ⟨w, hw_W, hw_dom⟩ := (ERC.satisfiedBy_iff_dominance r₁ α).mp (hr₁ α hα) l hl_L
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
-- § 12: Antimat — ERC Set → Antimatroid
-- ============================================================================

/-- `Antimat E` maps a consistent ERC set `E` to an antimatroid on
    `Fin n`. The ground set is `Fin n` (the constraint indices), and
    the feasible sets are `MChain(E)` — the subsets that appear in
    maximal chains consistent with `E`.

    [merchant-riggle-2016] Definition 6, Lemma 4. -/
def Antimat {n : Nat} (E : List (ERC n)) (hcons : ERCSet.Consistent E) :
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
      rw [← hk]; simp only [maximalChain, Set.mem_setOf_eq, Equiv.symm_apply_apply]; omega
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
        · simp only [Equiv.symm_apply_apply]; omega
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
      rw [← hk]; simp only [maximalChain, Set.mem_setOf_eq, Equiv.symm_apply_apply]; omega
    · -- S \ {r(k-1)} = maximalChain r (k-1)
      rw [← hk]; ext i; simp only [maximalChain, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        exact ⟨by omega, fun heq => by rw [heq] at h; simp only [Equiv.symm_apply_apply] at h; omega⟩
      · intro ⟨h1, h2⟩
        have : (r.symm i).val ≠ k.val - 1 := by
          intro heq
          have hsymm : r.symm i = ⟨k.val - 1, hkn1⟩ := Fin.ext heq
          exact h2 ((Equiv.apply_symm_apply r i).symm.trans (congrArg r.toFun hsymm))
        omega
  union_closed := fun S T hS hT => MChain.union_closed E hcons S T hS hT

-- ============================================================================
-- § 12b: The simple-ERC fragment — Birkhoff order ideals
-- ============================================================================

/-! ### Simple-ERC feasibility coincides with the antimatroid family

When every ERC is *simple* (one `W`, one `L` — a Hasse edge `w ≫ l`), the
constraints carry a genuine partial order and the decidable local condition
`Feasible` is exact: it agrees with the faithful `FeasiblePrefix`/`MChain` family.
This is the Birkhoff correspondence between order ideals of a poset and the
prefixes of its linear extensions ([merchant-riggle-2016]). For non-simple `E`
the agreement fails (`feasible_not_accessible`). -/

/-- **Birkhoff representation on the simple-ERC fragment.** With every ERC simple,
local feasibility coincides with the genuine antimatroid family: a set is locally
feasible iff it is a prefix of some consistent ranking. The forward direction is
the order-ideal ↔ linear-extension-prefix correspondence — reorder a witnessing
ranking `r₀` into the block `S` (in `r₀`'s order) followed by `Sᶜ` (in `r₀`'s
order); winner-uniqueness makes every Hasse edge respected, so the result
satisfies `E` and has `S` as its length-`|S|` prefix. -/
theorem feasible_iff_feasiblePrefix_of_simple {n : Nat} {E : List (ERC n)}
    (hcons : ERCSet.Consistent E) (hsimple : ERCSet.IsSimpleSet E) (S : Finset (Fin n)) :
    Feasible E S ↔ FeasiblePrefix E S := by
  refine ⟨fun hfeas => ?_, feasible_of_feasiblePrefix⟩
  obtain ⟨r₀, hr₀⟩ := hcons
  -- Two-block reordering of `r₀`: `S` first (in `r₀` order), then `Sᶜ`.
  have hcard : S.card + Sᶜ.card = n := by
    rw [Finset.card_add_card_compl]; exact Fintype.card_fin n
  have hScard : S.card ≤ n := le_trans (Finset.card_le_univ S) (le_of_eq (Fintype.card_fin n))
  let f : Fin n → Nat := fun i =>
    if i ∈ S then countBelow r₀ S i else S.card + countBelow r₀ Sᶜ i
  have hf_lt : ∀ i, f i < n := by
    intro i; simp only [f]; split_ifs with h
    · exact lt_of_lt_of_le (countBelow_lt_card r₀ S i h) hScard
    · have := countBelow_lt_card r₀ Sᶜ i (Finset.mem_compl.mpr h); omega
  let ff : Fin n → Fin n := fun i => ⟨f i, hf_lt i⟩
  have hff_inj : Function.Injective ff := by
    intro a b hab; simp only [ff, Fin.mk.injEq] at hab
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · simp only [f, if_pos ha, if_pos hb] at hab
      exact countBelow_injOn r₀ S a b ha hb hab
    · exfalso; simp only [f, if_pos ha, if_neg hb] at hab
      have := countBelow_lt_card r₀ S a ha; omega
    · exfalso; simp only [f, if_neg ha, if_pos hb] at hab
      have := countBelow_lt_card r₀ S b hb; omega
    · simp only [f, if_neg ha, if_neg hb] at hab
      exact countBelow_injOn r₀ Sᶜ a b
        (Finset.mem_compl.mpr ha) (Finset.mem_compl.mpr hb) (by omega)
  have hff_bij := Finite.injective_iff_bijective.mp hff_inj
  let e := Equiv.ofBijective ff hff_bij
  let r : Ranking n := e.symm
  have hr : ∀ i, (r.symm i : Nat) = f i := by
    intro i; show (e.symm.symm i : Nat) = f i; rw [Equiv.symm_symm]; rfl
  refine ⟨r, ?_, ⟨S.card, Nat.lt_succ_of_le hScard⟩, ?_⟩
  · -- `r` satisfies `E`.
    intro α hα
    rw [ERC.satisfiedBy_iff_dominance]
    intro l hl_L
    obtain ⟨⟨wα, hwαW, hwα_uniq⟩, _⟩ := hsimple α hα
    obtain ⟨w, hwW, hw_dom₀⟩ := (ERC.satisfiedBy_iff_dominance r₀ α).mp (hr₀ α hα) l hl_L
    have hdom₀ : (r₀.symm w : Nat) < (r₀.symm l : Nat) := hw_dom₀
    refine ⟨w, hwW, ?_⟩
    suffices h : f w < f l by
      show r.symm w < r.symm l
      rw [Fin.lt_def, hr w, hr l]; exact h
    simp only [f]
    by_cases hlS : l ∈ S
    · obtain ⟨w', hw'W, hw'S⟩ := hfeas α hα ⟨l, hl_L, hlS⟩
      obtain rfl : w = w' := (hwα_uniq w hwW).trans (hwα_uniq w' hw'W).symm
      rw [if_pos hw'S, if_pos hlS]
      exact countBelow_strict_mono r₀ S w l hw'S hlS hdom₀
    · by_cases hwS : w ∈ S
      · rw [if_pos hwS, if_neg hlS]
        have := countBelow_lt_card r₀ S w hwS; omega
      · rw [if_neg hwS, if_neg hlS]
        have := countBelow_strict_mono r₀ Sᶜ w l
          (Finset.mem_compl.mpr hwS) (Finset.mem_compl.mpr hlS) hdom₀
        omega
  · -- The length-`|S|` prefix of `r` is `S`.
    ext i
    rw [mem_prefixFinset, hr i]
    show f i < S.card ↔ i ∈ S
    simp only [f]
    split_ifs with h
    · exact iff_of_true (countBelow_lt_card r₀ S i h) h
    · exact iff_of_false (by omega) h

/-- The `Set`-level feasible family of the simple fragment: a set is the coercion
of a locally-feasible `Finset` iff it is `MChain`-feasible. (Bridges the decidable
`Finset` side to `Antimat`'s `Set`-valued `MChain` family.) -/
theorem feasible_coe_iff_mChain {n : Nat} {E : List (ERC n)}
    (hcons : ERCSet.Consistent E) (hsimple : ERCSet.IsSimpleSet E) (T : Set (Fin n)) :
    (∃ S' : Finset (Fin n), (↑S' : Set (Fin n)) = T ∧ Feasible E S') ↔ MChain E T := by
  constructor
  · rintro ⟨S', rfl, hfeas⟩
    exact (mChain_coe_iff_feasiblePrefix E S').mpr
      ((feasible_iff_feasiblePrefix_of_simple hcons hsimple S').mp hfeas)
  · rintro ⟨r, hr, k, hk⟩
    exact ⟨prefixFinset r k, (prefixFinset_coe r k).trans hk, feasible_of_satisfiedBy hr k⟩

/-- **The simple-ERC Birkhoff antimatroid.** A consistent set of simple ERCs
yields an antimatroid on `Fin n` whose feasible sets are the *locally feasible*
`Finset`s — the decidable form. On the simple fragment this family equals
`Antimat E`'s `MChain` family (`feasible_coe_iff_mChain`), so accessibility and
union closure transfer from `Antimat`; concrete membership is checked by `decide`
via `ofSimple_isFeasible_coe`. This is the order-ideal antimatroid of the
constraint partial order ([merchant-riggle-2016]). -/
def Antimat.ofSimple {n : Nat} (E : List (ERC n)) (hcons : ERCSet.Consistent E)
    (hsimple : ERCSet.IsSimpleSet E) : Antimatroid (Fin n) where
  E := Set.univ
  IsFeasible := fun T => ∃ S' : Finset (Fin n), (↑S' : Set (Fin n)) = T ∧ Feasible E S'
  empty_feasible := (feasible_coe_iff_mChain hcons hsimple ∅).mpr (Antimat E hcons).empty_feasible
  feasible_sub := fun T _ => Set.subset_univ T
  ground_feasible :=
    (feasible_coe_iff_mChain hcons hsimple Set.univ).mpr (Antimat E hcons).ground_feasible
  augmentation := fun T hT hne => by
    obtain ⟨x, hxE, hxT, hins⟩ := (Antimat E hcons).augmentation T
      ((feasible_coe_iff_mChain hcons hsimple T).mp hT) hne
    exact ⟨x, hxE, hxT, (feasible_coe_iff_mChain hcons hsimple _).mpr hins⟩
  removal := fun T hT hTne => by
    obtain ⟨x, hxT, hrem⟩ := (Antimat E hcons).removal T
      ((feasible_coe_iff_mChain hcons hsimple T).mp hT) hTne
    exact ⟨x, hxT, (feasible_coe_iff_mChain hcons hsimple _).mpr hrem⟩
  union_closed := fun S T hS hT =>
    (feasible_coe_iff_mChain hcons hsimple _).mpr
      ((Antimat E hcons).union_closed S T
        ((feasible_coe_iff_mChain hcons hsimple S).mp hS)
        ((feasible_coe_iff_mChain hcons hsimple T).mp hT))

/-- Concrete feasibility of `Antimat.ofSimple` is the decidable `Feasible` — the
hook that lets `decide` settle membership queries. -/
@[simp] theorem ofSimple_isFeasible_coe {n : Nat} {E : List (ERC n)}
    (hcons : ERCSet.Consistent E) (hsimple : ERCSet.IsSimpleSet E) (S : Finset (Fin n)) :
    (Antimat.ofSimple E hcons hsimple).IsFeasible (↑S : Set (Fin n)) ↔ Feasible E S := by
  constructor
  · rintro ⟨S', hS'eq, hfeas⟩; rwa [Finset.coe_inj.mp hS'eq] at hfeas
  · intro h; exact ⟨S, rfl, h⟩

-- ============================================================================
-- § 13: RCErc — Antimatroid → ERC Set
-- ============================================================================

open Classical in
/-- `RCErc` maps a rooted circuit of an antimatroid to an ERC.

    Given a rooted circuit `F : S(r)` with root `r` and carrier `S`:
    - `W(α) = S \ {r}` (constraints that must dominate `r`)
    - `L(α) = {r}` (the root)
    - `e(α) = G \ S` (constraints not in the carrier)

    [merchant-riggle-2016] Definition 10. -/
noncomputable def RCErc_single {n : Nat} (A : Antimatroid (Fin n))
    (rc : Antimatroid.RootedCircuit A) : ERC n :=
  fun k =>
    if k ∈ rc.carrier ∧ k ≠ rc.root then .W
    else if k = rc.root then .L
    else .e

/-- `RCErc A` is the ERC set of antimatroid `A`: the image of `A`'s rooted
    circuits under `RCErc_single`. This is the inverse of `Antimat`
    ([merchant-riggle-2016] Theorems 1–2).

    Represented as a `Set (ERC n)`; a ranking `r` *satisfies* `RCErc A` when
    `∀ α ∈ RCErc A, ERC.SatisfiedBy r α` — the `Set` analogue of
    `ERCSet.SatisfiedBy`, used to state the isomorphism theorems below. -/
noncomputable def RCErc {n : Nat} (A : Antimatroid (Fin n)) : Set (ERC n) :=
  Set.range (RCErc_single A)

/-- **Two-element rooted circuits are simple ERCs.** A rooted circuit with a
two-element carrier `{w, l}` rooted at `l` maps under `RCErc_single` to the simple
ERC `simpleERC w l` (the Hasse edge `w ≫ l`). Larger carriers instead give a
*disjunctive*, multi-`W` ERC — one `L` (the root) requiring *some* element of
`S \ {root}` to dominate it — which is exactly the "beyond partial orders" content
that makes the local `Feasible` predicate inexact (`feasible_not_accessible`). -/
theorem RCErc_single_eq_simpleERC {n : Nat} (A : Antimatroid (Fin n))
    (rc : Antimatroid.RootedCircuit A) {w l : Fin n}
    (hcarrier : rc.carrier = {w, l}) (hroot : rc.root = l) (hwl : w ≠ l) :
    RCErc_single A rc = simpleERC w l := by
  funext k
  simp only [RCErc_single, simpleERC, hcarrier, hroot, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  by_cases hkw : k = w <;> by_cases hkl : k = l <;> simp_all

-- ============================================================================
-- § 14: Isomorphism Theorems
-- ============================================================================

/-- **Theorem 1** ([merchant-riggle-2016]): `Antimat` is a left inverse of
    `RCErc`. For any antimatroid `A`, rebuilding from `A`'s rooted-circuit
    ERCs recovers `A` — stated at the feasible-set level (`Antimat (RCErc A)`
    and `A` have the same feasible sets), since `Antimat`'s feasible sets are
    by definition the maximal chains satisfying the ERC set.

    The general proof rests on the rooted-circuit characterization of an
    antimatroid's feasible sets ([dietrich-1987]; [merchant-riggle-2016]
    Lemmas 7, 9), which is why this direction carries an honest `sorry`. -/
theorem Antimat_RCErc_inv {n : Nat} (A : Antimatroid (Fin n)) (S : Set (Fin n)) :
    A.IsFeasible S ↔
      ∃ r : Ranking n, (∀ α ∈ RCErc A, ERC.SatisfiedBy r α) ∧
        ∃ k, maximalChain r k = S := by
  -- TODO: [merchant-riggle-2016] Theorem 1 (antimatroid → ERC direction of
  -- the isomorphism). Show A's feasible sets are exactly the maximal chains
  -- consistent with A's rooted-circuit ERCs. Requires [dietrich-1987]'s
  -- rooted-circuit characterization (the hard direction via traces).
  sorry

/-- **Theorem 2** ([merchant-riggle-2016]): `RCErc` is a left inverse of `Antimat`
    *up to entailment*. For a consistent ERC set `E`, the rooted-circuit ERCs of
    `Antimat E` pick out exactly `E`'s satisfying rankings — they are *logically
    equivalent* to `E`, not literally equal.

    Literal set equality (`RCErc (Antimat E) = {α | α ∈ E}`) is **false** by
    transitive-reduction ambiguity: `RCErc (Antimat [a≫b, b≫c])` also contains the
    implied edge `a≫c` (a rooted circuit of the chain antimatroid), a strict
    superset of the two-edge input — yet both pick out the single order `a≫b≫c`.
    Hence the statement is mutual entailment (same satisfying rankings), the form
    [merchant-riggle-2016] actually proves. The general proof rests on
    [dietrich-1987]'s rooted-circuit characterization (via Lemmas 7, 9), so it
    carries an honest `sorry`. -/
theorem RCErc_Antimat_inv {n : Nat} (E : List (ERC n))
    (hcons : ERCSet.Consistent E) :
    ∀ r : Ranking n,
      (∀ α ∈ RCErc (Antimat E hcons), ERC.SatisfiedBy r α) ↔ ERCSet.SatisfiedBy r E := by
  -- TODO: [merchant-riggle-2016] Theorem 2 (logical-equivalence form). Needs the
  -- rooted-circuit characterization of `Antimat E`'s feasible sets ([dietrich-1987];
  -- [merchant-riggle-2016] Lemmas 7, 9).
  sorry

/-- **Theorem 3** ([merchant-riggle-2016]): `Antimat` preserves
    entailment.

    If ERC set `E` entails `F` (every ranking satisfying `E` also
    satisfies `F`), then `Antimat(E) ⊆ Antimat(F)` (every feasible
    set of `Antimat(E)` is also feasible in `Antimat(F)`). -/
theorem Antimat_entailment {n : Nat} (E F : List (ERC n))
    (hE : ERCSet.Consistent E) (hF : ERCSet.Consistent F)
    (h : ERCSet.Entails E F) :
    ∀ S, (Antimat E hE).IsFeasible S → (Antimat F hF).IsFeasible S := by
  intro S ⟨r, hr, k, hk⟩
  exact ⟨r, h r hr, k, hk⟩

/-- **Theorem 4** ([merchant-riggle-2016]): `RCErc` preserves
    containment.

    If antimatroid `A ⊆ B` (every feasible set of `A` is feasible in
    `B`), then `RCErc(A)` entails `RCErc(B)`. -/
theorem RCErc_entailment {n : Nat} (A B : Antimatroid (Fin n))
    (h : ∀ S, A.IsFeasible S → B.IsFeasible S) :
    ∀ r : Ranking n, (∀ α ∈ RCErc A, ERC.SatisfiedBy r α) →
      (∀ α ∈ RCErc B, ERC.SatisfiedBy r α) := by
  -- TODO: [merchant-riggle-2016] Theorem 4 (mirror of `Antimat_entailment`).
  -- Feasible-set containment A ⊆ B becomes ERC entailment RCErc A ⊨ RCErc B;
  -- needs the rooted-circuit ↔ feasible-set correspondence of Theorem 1
  -- ([dietrich-1987]; [merchant-riggle-2016] Lemmas 7, 9).
  sorry

-- ============================================================================
-- § 15: Rankings as maximal chains
-- ============================================================================

/-! ### Rankings as maximal chains

A ranking is the same data as a maximal chain in the boolean lattice `2^(Fin n)`:
its sequence of prefixes `∅ ⊂ … ⊂ univ`, each step adding the next-ranked
constraint. The design deliberately keeps this order-theoretic content *outside*
the type of `Ranking` (which stays a permutation, [merchant-riggle-2016]):
`rankingChainEquiv` records the bijection without retyping rankings as chains. -/

/-- The prefix `∅` at height `0`. -/
theorem prefixFinset_zero {n : Nat} (r : Ranking n) : prefixFinset r 0 = ∅ := by
  ext i; simp [mem_prefixFinset]

/-- The constraint at rank position `k` is the new element added passing from the
height-`k` prefix to the height-`k+1` prefix. -/
theorem prefixFinset_succ_eq {n : Nat} (r : Ranking n) (k : Fin n) :
    prefixFinset r k.succ = insert (r k) (prefixFinset r k.castSucc) := by
  ext i
  simp only [mem_prefixFinset, Finset.mem_insert, Fin.val_succ, Fin.val_castSucc]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact Or.inr h'
    · refine Or.inl ?_
      have hk : r.symm i = k := Fin.ext h'
      rw [← hk, Equiv.apply_symm_apply]
  · rintro (rfl | h')
    · rw [Equiv.symm_apply_apply]; omega
    · omega

theorem prefixFinset_apply_notMem {n : Nat} (r : Ranking n) (k : Fin n) :
    r k ∉ prefixFinset r k.castSucc := by
  simp [mem_prefixFinset, Equiv.symm_apply_apply]

private theorem insert_eq_of_notMem {α : Type*} [DecidableEq α] {s : Finset α}
    {x y : α} (hx : x ∉ s) (h : insert x s = insert y s) : x = y := by
  have hmem : x ∈ insert y s := h ▸ Finset.mem_insert_self x s
  rcases Finset.mem_insert.mp hmem with h1 | h1
  · exact h1
  · exact absurd h1 hx

/-- A **maximal chain** in the boolean lattice `2^(Fin n)`: an ascending family of
finsets from `∅`, each step adding exactly one new element (so it reaches `univ` at
the top, `toFun_last`). -/
@[ext] structure MaximalChain (n : ℕ) where
  /-- The chain, indexed by height `0 … n`. -/
  toFun : Fin (n + 1) → Finset (Fin n)
  /-- The chain starts at the empty set. -/
  bot : toFun 0 = ∅
  /-- Each step adds exactly one new element. -/
  step : ∀ k : Fin n, ∃ x, x ∉ toFun k.castSucc ∧ toFun k.succ = insert x (toFun k.castSucc)

namespace MaximalChain

variable {n : ℕ} (C : MaximalChain n)

/-- The unique element added at step `k`. -/
noncomputable def added (k : Fin n) : Fin n := Classical.choose (C.step k)

theorem added_notMem (k : Fin n) : C.added k ∉ C.toFun k.castSucc :=
  (Classical.choose_spec (C.step k)).1

theorem toFun_succ (k : Fin n) :
    C.toFun k.succ = insert (C.added k) (C.toFun k.castSucc) :=
  (Classical.choose_spec (C.step k)).2

/-- A constraint is in the height-`k` prefix iff it was added at some earlier step. -/
theorem mem_toFun_iff (k : Fin (n + 1)) (i : Fin n) :
    i ∈ C.toFun k ↔ ∃ j : Fin n, j.val < k.val ∧ C.added j = i := by
  induction k using Fin.induction with
  | zero => simp [C.bot]
  | succ k ih =>
    rw [C.toFun_succ, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨k, by simp [Fin.val_succ], rfl⟩
      · exact ⟨j, by simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢; omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rw [Fin.val_succ] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inr ⟨j, by simpa [Fin.val_castSucc] using h, rfl⟩
      · exact Or.inl (by rw [show j = k from Fin.ext (by simpa using h)])

theorem added_injective : Function.Injective C.added := by
  intro a b hab
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · refine absurd ?_ (C.added_notMem b)
    rw [← hab]
    exact (C.mem_toFun_iff b.castSucc (C.added a)).mpr ⟨a, by simpa using h, rfl⟩
  · exact Fin.ext h
  · refine absurd ?_ (C.added_notMem a)
    rw [hab]
    exact (C.mem_toFun_iff a.castSucc (C.added b)).mpr ⟨b, by simpa using h, rfl⟩

theorem added_bijective : Function.Bijective C.added :=
  Finite.injective_iff_bijective.mp C.added_injective

/-- A maximal chain reaches the full ground set at its top. -/
theorem toFun_last : C.toFun (Fin.last n) = Finset.univ := by
  ext i
  simp only [C.mem_toFun_iff, Finset.mem_univ, iff_true, Fin.val_last]
  obtain ⟨j, hj⟩ := C.added_bijective.surjective i
  exact ⟨j, j.isLt, hj⟩

/-- The ranking recovered from a maximal chain: position `k` holds the element
added at step `k`. -/
noncomputable def toRanking : Ranking n := Equiv.ofBijective C.added C.added_bijective

theorem toRanking_apply (k : Fin n) : C.toRanking k = C.added k := rfl

theorem added_toRanking_symm (i : Fin n) : C.added (C.toRanking.symm i) = i := by
  have h := C.toRanking.apply_symm_apply i
  rwa [toRanking_apply] at h

/-- The prefixes of the recovered ranking are the original chain. -/
theorem prefixFinset_toRanking (k : Fin (n + 1)) :
    prefixFinset C.toRanking k = C.toFun k := by
  ext i
  rw [mem_prefixFinset, C.mem_toFun_iff]
  constructor
  · intro h
    exact ⟨C.toRanking.symm i, h, C.added_toRanking_symm i⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : C.toRanking.symm (C.added j) = j := by
      rw [← toRanking_apply]; exact C.toRanking.symm_apply_apply j
    rw [hj']; exact hj

end MaximalChain

/-- The maximal chain of a ranking: its sequence of prefixes. -/
def prefixChain {n : Nat} (r : Ranking n) : MaximalChain n where
  toFun := prefixFinset r
  bot := prefixFinset_zero r
  step := fun k => ⟨r k, prefixFinset_apply_notMem r k, prefixFinset_succ_eq r k⟩

/-- **Rankings are maximal chains** ([merchant-riggle-2016]). A ranking and the
maximal chain of its prefixes carry the same information — the "ranking is a chain"
intuition, as a bijection rather than a retyping of `Ranking`. -/
noncomputable def rankingChainEquiv (n : ℕ) : Ranking n ≃ MaximalChain n where
  toFun := prefixChain
  invFun := MaximalChain.toRanking
  left_inv r := by
    apply Equiv.ext
    intro k
    rw [MaximalChain.toRanking_apply]
    refine insert_eq_of_notMem ((prefixChain r).added_notMem k) ?_
    rw [← (prefixChain r).toFun_succ]
    exact prefixFinset_succ_eq r k
  right_inv C := MaximalChain.ext (funext fun k => C.prefixFinset_toRanking k)

end OptimalityTheory

import Linglib.Core.Constraint.OT.ERC
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# OT — Antimatroids and the ERC–Antimatroid Isomorphism

Antimatroids are combinatorial structures that generalize the notion of
a partial order. They were first described by @cite{dilworth-1940} in
the context of lattice theory and have been rediscovered many times
under different names (see @cite{korte-lovasz-schrader-1991} for a
comprehensive survey).

For Optimality Theory, antimatroids are significant because
@cite{merchant-riggle-2016} prove that consistent ERC sets over `n`
constraints are isomorphic to antimatroids on `Fin n`. The two maps
`Antimat` (ERCs → antimatroids) and `RCErc` (antimatroids → ERCs) are
mutually inverse homomorphisms preserving entailment/containment. Any
result about antimatroids transfers immediately to OT: learning
algorithms, typological classification, complexity bounds.

## Definitions (general antimatroid theory)

Following @cite{merchant-riggle-2016} Definitions 2–5:

- `SetSystem` — a ground set `G` with a collection `F` of feasible subsets
- `AccessibleSetSystem` — augmentation + removal properties
- `Antimatroid` — accessible set system closed under union

The design follows mathlib's `Matroid` pattern: bundled structure with
`Set α` ground set and `Prop` axioms.

## ERC → Antimatroid pipeline

- `MChain` — maps a consistent ERC set to its feasible sets (Definition 1)
- `Antimat` — maps a consistent ERC set to an antimatroid (Definition 6)
- `RCErc` — maps an antimatroid to an ERC set (Definition 10)

## Lemmas

- `maximalChain_dominance` — prefix sets are downward-closed under dominance
- `MChain.union_closed` — Lemma 3: MChain is union-closed

## Theorems

- `Antimat_entailment` — Theorem 3: entailment → containment (proved)
- `Antimat_RCErc_inv` — Theorem 1 (placeholder)
- `RCErc_Antimat_inv` — Theorem 2 (placeholder)
- `RCErc_entailment` — Theorem 4 (placeholder)

## References

@cite{dilworth-1940} — Lattices with unique irreducible decompositions
@cite{korte-lovasz-schrader-1991} — Greedoids
@cite{merchant-riggle-2016} — OT grammars, beyond partial orders:
ERC sets and antimatroids
-/

namespace Core.Constraint.OT

-- ============================================================================
-- § 1: Set System (Definition 2)
-- ============================================================================

/-- A **set system** `(G, F)` is a finite ground set `G` with a
    collection `F` of subsets of `G`, called **feasible sets**.

    Any subset of a power set is a set system. The feasible sets are
    the subsets of `G` that the system "recognizes." -/
structure SetSystem (α : Type*) where
  /-- The ground set. -/
  E : Set α
  /-- The feasible set predicate: `IsFeasible S` means `S` is a
      recognized subset of the ground set. -/
  IsFeasible : Set α → Prop
  /-- The empty set is always feasible. -/
  empty_feasible : IsFeasible ∅
  /-- Feasible sets are subsets of the ground set. -/
  feasible_sub : ∀ S, IsFeasible S → S ⊆ E

-- ============================================================================
-- § 2: Accessible Set System (Definition 3)
-- ============================================================================

/-- An **accessible set system** is a set system with augmentation and
    removal properties. Informally:

    - **Augmentation**: any feasible set that isn't the full ground set
      can be extended by adding one element to produce another feasible set.
    - **Removal**: any non-empty feasible set can be shrunk by removing
      one element to produce another feasible set.

    The term "accessible" refers to the fact that both the empty set and
    the ground set are reachable from any feasible set via single-element
    additions or removals.

    @cite{merchant-riggle-2016} Definition 3. -/
structure AccessibleSetSystem (α : Type*) extends SetSystem α where
  /-- The ground set is feasible. -/
  ground_feasible : IsFeasible E
  /-- **Augmentation**: every feasible set that is not the ground set
      can be extended by adding one element from `E` to produce another
      feasible set. -/
  augmentation : ∀ S, IsFeasible S → S ≠ E →
    ∃ x ∈ E, x ∉ S ∧ IsFeasible (insert x S)
  /-- **Removal**: every non-empty feasible set can be shrunk by
      removing one element to produce another feasible set. -/
  removal : ∀ S, IsFeasible S → S.Nonempty →
    ∃ x ∈ S, IsFeasible (S \ {x})

-- ============================================================================
-- § 3: Antimatroid (Definition 5)
-- ============================================================================

/-- An **antimatroid** is an accessible set system that is closed under
    union: the union of any two feasible sets is also feasible.

    This is the structure that @cite{merchant-riggle-2016} prove is
    isomorphic to consistent ERC sets. The three defining properties —
    accessibility (augmentation + removal) and union closure — correspond
    exactly to the combinatorial structure of OT ranking spaces.

    The design follows mathlib's `Matroid`: bundled structure (not a
    typeclass), `Set α` ground set, `Prop` axioms.

    @cite{merchant-riggle-2016} Definition 5. -/
structure Antimatroid (α : Type*) extends AccessibleSetSystem α where
  /-- **Union closure**: the union of any two feasible sets is feasible.

      This property distinguishes antimatroids from arbitrary accessible
      set systems. It corresponds to the fact that consistent ERC sets
      have "disjunctive" ranking requirements — if two partial rankings
      are consistent, their union (combining their requirements) is also
      consistent. -/
  union_closed : ∀ S T, IsFeasible S → IsFeasible T → IsFeasible (S ∪ T)

-- ============================================================================
-- § 4: Finiteness
-- ============================================================================

/-- An antimatroid with a finite ground set. Following mathlib's
    `Matroid.Finite`, this is a typeclass so it can be inferred. -/
class Antimatroid.Finite {α : Type*} (A : Antimatroid α) : Prop where
  ground_finite : A.E.Finite

theorem Antimatroid.ground_finite {α : Type*} (A : Antimatroid α)
    [A.Finite] : A.E.Finite :=
  Antimatroid.Finite.ground_finite

-- ============================================================================
-- § 5: Basic Properties
-- ============================================================================

variable {α : Type*}

/-- The ground set of an antimatroid is feasible. -/
theorem Antimatroid.ground_isFeasible (A : Antimatroid α) :
    A.IsFeasible A.E :=
  A.ground_feasible

/-- The empty set is feasible in any antimatroid. -/
theorem Antimatroid.empty_isFeasible (A : Antimatroid α) :
    A.IsFeasible ∅ :=
  A.empty_feasible

/-- Singletons in the ground set are feasible in any antimatroid.

    Proof: the empty set is feasible and not equal to `E` (since `E`
    contains `x`), so by augmentation there exists some `y ∈ E` with
    `{y}` feasible. By induction (via removal from larger sets), every
    singleton is feasible.

    For now, we prove only the weaker statement that some singleton
    exists. -/
theorem Antimatroid.exists_singleton_feasible (A : Antimatroid α)
    (hne : A.E.Nonempty) : ∃ x ∈ A.E, A.IsFeasible {x} := by
  have hne_ground : (∅ : Set α) ≠ A.E := by
    intro h; obtain ⟨x, hx⟩ := hne; simp [← h] at hx
  obtain ⟨x, hx_mem, _, hx_feas⟩ := A.augmentation ∅ A.empty_feasible hne_ground
  have : insert x (∅ : Set α) = {x} := by ext; simp
  rw [this] at hx_feas
  exact ⟨x, hx_mem, hx_feas⟩

-- ============================================================================
-- § 6: The Free Antimatroid
-- ============================================================================

/-- The **free antimatroid** on a set `E`: every subset is feasible.

    This corresponds to the OT system with no ranking requirements
    (the empty ERC set) — all `n!` rankings are consistent.
    @cite{merchant-riggle-2016} Definition 8. -/
def Antimatroid.free (E : Set α) : Antimatroid α where
  E := E
  IsFeasible := fun S => S ⊆ E
  empty_feasible := Set.empty_subset E
  feasible_sub := fun _ h => h
  ground_feasible := Set.Subset.refl E
  augmentation := fun S hS hne => by
    obtain ⟨x, hxE, hxS⟩ : ∃ x, x ∈ E ∧ x ∉ S := by
      by_contra h
      apply hne
      ext x
      constructor
      · intro hx; exact hS hx
      · intro hx
        by_contra hxS
        exact h ⟨x, hx, hxS⟩
    exact ⟨x, hxE, hxS, Set.insert_subset hxE hS⟩
  removal := fun S hS hne => by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, Set.diff_subset.trans hS⟩
  union_closed := fun _ _ hS hT => Set.union_subset hS hT

/-- The free antimatroid on `E` has `IsFeasible S ↔ S ⊆ E`. -/
theorem Antimatroid.free_isFeasible (E : Set α) (S : Set α) :
    (Antimatroid.free E).IsFeasible S ↔ S ⊆ E :=
  Iff.rfl

-- ============================================================================
-- § 7: Traces (Definition 7)
-- ============================================================================

/-- The **trace** of antimatroid `A` on subset `S ⊆ E` is the
    antimatroid `(S, {f ∩ S | f ∈ F})` — restricting the feasible
    sets to their intersections with `S`.

    Traces capture the ordering relations that the original antimatroid
    places on the constraints in `S`.

    @cite{merchant-riggle-2016} Definition 7. -/
def Antimatroid.trace (A : Antimatroid α) (S : Set α) (_hS : S ⊆ A.E) :
    SetSystem α where
  E := S
  IsFeasible := fun T => ∃ F, A.IsFeasible F ∧ T = F ∩ S
  empty_feasible := ⟨∅, A.empty_feasible, by simp⟩
  feasible_sub := fun T ⟨F, _, hT⟩ => hT ▸ Set.inter_subset_right

-- ============================================================================
-- § 8: Rooted Circuits (Definition 9)
-- ============================================================================

/-- A **rooted circuit** of antimatroid `A` on `S ⊆ E` is a trace
    `A : S` such that every proper subset of `S` gives a free trace
    (no ordering constraints), but `A : S` itself is not free.

    Rooted circuits are the minimal subsets of `E` that encode actual
    ranking requirements. Each rooted circuit corresponds to exactly
    one ERC under the `RCErc` map.

    The **root** of the circuit is the unique element `r ∈ S` such that
    `{r}` is not feasible in `A : S`.

    @cite{merchant-riggle-2016} Definition 9. -/
structure Antimatroid.RootedCircuit (A : Antimatroid α) where
  /-- The set defining the circuit. -/
  carrier : Set α
  /-- The carrier is a subset of the ground set. -/
  carrier_sub : carrier ⊆ A.E
  /-- The root element. -/
  root : α
  /-- The root is in the carrier. -/
  root_mem : root ∈ carrier
  /-- The trace on the carrier is not free: `{root}` is not feasible
      in the trace. -/
  not_free : ¬ (A.trace carrier carrier_sub).IsFeasible {root}
  /-- Every proper subset of the carrier gives a free trace:
      for every `T ⊂ carrier` and `x ∈ T`, the singleton `{x}` is
      feasible in the trace `A : T`. -/
  proper_free : ∀ T : Set α, ∀ hT : T ⊂ carrier,
    ∀ x ∈ T,
      (A.trace T (hT.subset.trans carrier_sub)).IsFeasible {x}

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

    @cite{merchant-riggle-2016} Definition 1. -/
def MChain {n : Nat} (E : List (ERC n)) : Set (Fin n) → Prop :=
  fun S => ∃ r : Ranking n, ERCSet.satisfiedBy r E ∧
    ∃ k : Fin (n + 1), maximalChain r k = S

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
-- § 12: Antimat — ERC Set → Antimatroid
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
-- § 13: RCErc — Antimatroid → ERC Set
-- ============================================================================

open Classical in
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
-- § 14: Isomorphism Theorems
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

end Core.Constraint.OT

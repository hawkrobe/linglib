module

public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Core.Probability.Decision.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.FieldSimp

/-!
# Merin (1999): Negative Attributes, Partitions, and Rational Decisions

This file formalizes the decision-theoretic rationale in [merin-1999] for attribute spaces
being partitions and its epistemic, syntax-independent characterization of negative
attributes as proper coarsenings. The complements of a partition's cells form a partition
exactly when the partition is binary (FACT 1, `compl_isPartition_iff`); under a probability
measure the complement probabilities sum to one less than the number of cells, so they form a
distribution exactly for two cells (FACTs 2 and 3, `sum_measureReal_compl`,
`sum_measureReal_compl_eq_one_iff`); the partition of a cell and its complement is the coarsest
coarsening preserving the cell (FACT 4, `isGreatest_polar_cell`); an attribute is negative with
respect to a partition when its complement is a cell and its polar partition properly coarsens
the partition (`IsNegativeAttribute`); and expected utility computed cell by cell does not depend
on the partition (`eu_eq_partitionEU`, `partitionEU_congr`).

## Implementation notes

Coarsening is the refinement order on `Setoid`. Expected utility uses
`Core.DecisionTheory.DecisionProblem`, with the prior independent of the act; the paper's
computation for coarsenings uses Jeffrey's form, with probabilities conditional on the act.

## TODO

The paper's point that under a coarsening each coarse cell's term is the sum of the terms of the
finer cells it contains, and FACT 5, that re-coverings which neither coarsen nor refine admit no
such regrouping, are not formalized; nor is the conditional-independence result of
[johnson-1986] that the paper cites.

## References

* [merin-1999]
* [johnson-1986]
-/

@[expose] public section

namespace Merin1999b

open Core.DecisionTheory Core.DecisionTheory.DecisionProblem

/-! ### FACT 1: complement families -/

/-- FACT 1 ([merin-1999] p. 261): for a partition `F` of a
nonempty type, the complements of its cells form a partition iff `F`
has exactly two cells. -/
theorem compl_isPartition_iff {W : Type*} [Nonempty W] {F : Set (Set W)}
    (hF : Setoid.IsPartition F) :
    Setoid.IsPartition (compl '' F) ↔ F.encard = 2 := by
  have cover : ∀ a : W, ∃ B ∈ F, a ∈ B := fun a ↦
    let ⟨B, hB, _⟩ := hF.2 a; ⟨B, hB.1, hB.2⟩
  have uniq : ∀ {a : W} {B₁ B₂ : Set W}, B₁ ∈ F → B₂ ∈ F →
      a ∈ B₁ → a ∈ B₂ → B₁ = B₂ := by
    intro a B₁ B₂ h1 h2 ha1 ha2
    obtain ⟨B, _, hu⟩ := hF.2 a
    rw [hu B₁ ⟨h1, ha1⟩, hu B₂ ⟨h2, ha2⟩]
  constructor
  · intro hFc
    -- A first cell, through an arbitrary point.
    obtain ⟨A, hA, haA⟩ := cover (Classical.arbitrary W)
    -- A second cell: `Aᶜ ≠ ∅` (it is a cell of the complement
    -- partition), so some point lies outside `A`.
    have hAc : Aᶜ ∈ compl '' F := Set.mem_image_of_mem _ hA
    obtain ⟨b, hb⟩ : Set.Nonempty (Aᶜ) :=
      Set.nonempty_iff_ne_empty.mpr (fun h ↦ hFc.1 (h ▸ hAc))
    obtain ⟨B, hB, hbB⟩ := cover b
    have hBA : B ≠ A := fun h ↦ hb (h ▸ hbB)
    -- No third cell: its points would witness overlap of `Aᶜ` and `Bᶜ`.
    have hall : ∀ C ∈ F, C = A ∨ C = B := by
      intro C hC
      by_contra hne
      push Not at hne
      obtain ⟨hCA, hCB⟩ := hne
      obtain ⟨c, hc⟩ : Set.Nonempty C :=
        Set.nonempty_iff_ne_empty.mpr (fun h ↦ hF.1 (h ▸ hC))
      have hcA : c ∈ Aᶜ := fun h ↦ hCA (uniq hC hA hc h)
      have hcB : c ∈ Bᶜ := fun h ↦ hCB (uniq hC hB hc h)
      obtain ⟨D, _, hu⟩ := hFc.2 c
      have h1 := hu Aᶜ ⟨Set.mem_image_of_mem _ hA, hcA⟩
      have h2 := hu Bᶜ ⟨Set.mem_image_of_mem _ hB, hcB⟩
      exact hBA (compl_inj_iff.mp (h2.trans h1.symm))
    have hFeq : F = {A, B} := by
      ext C
      constructor
      · intro hC
        rcases hall C hC with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ rfl
      · rintro (rfl | rfl)
        · exact hA
        · exact hB
    rw [hFeq]
    exact Set.encard_pair (Ne.symm hBA)
  · intro h2
    obtain ⟨A, B, hAB, rfl⟩ := Set.encard_eq_two.mp h2
    have hA : A ∈ ({A, B} : Set (Set W)) := Set.mem_insert _ _
    have hB : B ∈ ({A, B} : Set (Set W)) := Set.mem_insert_of_mem _ rfl
    -- In a binary partition the two cells are mutual complements.
    have hcompl : Aᶜ = B := by
      ext a
      constructor
      · intro haAc
        rcases cover a with ⟨C, hC, haC⟩
        rcases hC with rfl | rfl
        · exact absurd haC haAc
        · exact haC
      · intro haB haA
        exact hAB (uniq hA hB haA haB)
    have hcompl' : Bᶜ = A := by rw [← hcompl, compl_compl]
    have himg : compl '' {A, B} = {A, B} := by
      rw [Set.image_pair, hcompl, hcompl', Set.pair_comm]
    rw [himg]
    exact hF

/-! ### FACTs 2 and 3: complement probabilities -/

section Probability

open MeasureTheory

variable {M : Type*} [MeasurableSpace M] (μ : Measure M) [IsProbabilityMeasure μ]
  {F : Finset (Set M)}

/-- FACT 3 ([merin-1999] p. 261): under a probability measure, the probabilities of the
complements of the `n` cells of a finite partition sum to `n − 1`. -/
theorem sum_measureReal_compl (hF : Setoid.IsPartition (F : Set (Set M)))
    (hm : ∀ c ∈ F, MeasurableSet c) :
    ∑ c ∈ F, μ.real cᶜ = F.card - 1 := by
  have hsum : ∑ c ∈ F, μ.real c = 1 := by
    have h := measureReal_biUnion_finset (μ := μ) hF.pairwiseDisjoint hm
    simp only [id] at h
    rw [← h, ← Finset.set_biUnion_coe, ← Set.sUnion_eq_biUnion, hF.sUnion_eq_univ, probReal_univ]
  rw [Finset.sum_congr rfl fun c hc ↦ probReal_compl_eq_one_sub (hm c hc),
    Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- FACT 3's second clause ([merin-1999] p. 261): the complement probabilities sum to one iff the
partition has two cells. Hence FACT 2: for more than two cells they are not a probability
distribution. -/
theorem sum_measureReal_compl_eq_one_iff (hF : Setoid.IsPartition (F : Set (Set M)))
    (hm : ∀ c ∈ F, MeasurableSet c) :
    ∑ c ∈ F, μ.real cᶜ = 1 ↔ F.card = 2 := by
  rw [sum_measureReal_compl μ hF hm]
  constructor
  · intro h
    exact_mod_cast (by linarith : (F.card : ℝ) = 2)
  · intro h
    rw [h]
    norm_num

end Probability

/-! ### Coarsening and negative attributes -/

/-- Q properly coarsens Q': Q is strictly coarser than Q' in the refinement order, which over
a finite domain is coarsening with strictly fewer cells ([merin-1999] p. 262 definition). -/
def IsProperCoarsening {M : Type*} (q q' : Setoid M) : Prop := q' < q

/-- FACT 4 ([merin-1999] p. 263): for a cell P of a partition, the partition {P, ¬P} is the
coarsest coarsening of it that preserves P, i.e. that decides P. -/
theorem isGreatest_polar_cell {M : Type*} (q : Setoid M) (w : M) :
    IsGreatest {q' | q ≤ q' ∧ q'.Decides (q.cell w)} (Setoid.polar (q.cell w)) :=
  ⟨⟨Setoid.decides_cell w, Setoid.polar_decides⟩, fun _ h ↦ h.2⟩

/-- `R` is a **negative attribute** with respect to `q` ([merin-1999] p. 263): the complement
of `R` is a cell of `q`, and the two-cell partition `{R, ¬R}` properly coarsens `q`. Negativity
is epistemic (partition-kinetic), not morphological. -/
def IsNegativeAttribute {M : Type*} (R : Set M) (q : Setoid M) : Prop :=
  (∃ w, q.cell w = Rᶜ) ∧ IsProperCoarsening (Setoid.polar R) q

/-! ### EU compositionality under coarsening -/

variable {K M A : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Expected utility computed via a partition: weight each cell's conditional EU by the
cell's probability (`EU_Q(a) = Σ_{c ∈ cells Q} P(c) · EU(a | c)`). -/
def partitionEU [Fintype M] [DecidableEq M] (dp : DecisionProblem K M A) (q : Setoid M)
    [DecidableRel q] (a : A) : K :=
  ∑ cell ∈ (Finpartition.ofSetoid q).parts, cell.sum dp.prior * condExpectedUtility dp cell a

/-- Cell probability times conditional EU is the raw weighted sum, for non-negative priors. -/
private theorem cellProb_mul_conditionalEU [DecidableEq M]
    (dp : DecisionProblem K M A) (cell : Finset M) (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cell.sum dp.prior * condExpectedUtility dp cell a =
    cell.sum (fun w ↦ dp.prior w * dp.utility w a) := by
  simp only [condExpectedUtility]
  by_cases htot : cell.sum dp.prior = 0
  · simp only [htot, ite_true, mul_zero]
    symm; apply Finset.sum_eq_zero; intro w hw
    have hle : dp.prior w ≤ cell.sum dp.prior :=
      Finset.single_le_sum (fun x _ ↦ hprior x) hw
    have hzero : dp.prior w = 0 := le_antisymm (by linarith) (hprior w)
    simp [hzero]
  · simp only [htot, ite_false]
    rw [Finset.mul_sum]
    congr 1; ext w; field_simp

/-- Law of total expectation: the unconditional expected utility equals the
partition-relative EU, for any partition (non-negative priors). -/
theorem eu_eq_partitionEU [Fintype M] [DecidableEq M] (dp : DecisionProblem K M A) (a : A)
    (q : Setoid M) [DecidableRel q] (hprior : ∀ w, dp.prior w ≥ 0) :
    expectedUtility dp a = partitionEU dp q a := by
  simp only [expectedUtility, partitionEU]
  conv_lhs => rw [← (Finpartition.ofSetoid q).biUnion_parts]
  rw [Finset.sum_biUnion (Finpartition.ofSetoid q).supIndep.pairwiseDisjoint]
  exact Finset.sum_congr rfl (fun cell _ ↦ (cellProb_mul_conditionalEU dp cell a hprior).symm)

/-- Partition-relative EU does not depend on the partition: any two partitions compute the
unconditional EU. -/
theorem partitionEU_congr [Fintype M] [DecidableEq M] (dp : DecisionProblem K M A)
    (q q' : Setoid M) [DecidableRel q] [DecidableRel q'] (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionEU dp q a = partitionEU dp q' a :=
  (eu_eq_partitionEU dp a q hprior).symm.trans (eu_eq_partitionEU dp a q' hprior)

end Merin1999b

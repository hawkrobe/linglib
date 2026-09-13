import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Core.Probability.Decision.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.FieldSimp

/-!
# Merin (1999): Negative Attributes, Partitions, and Rational Decisions

This file formalizes the decision-theoretic rationale in [merin-1999] for attribute spaces
being partitions and its epistemic, syntax-independent characterization of negative
attributes as proper coarsenings. The complements of a partition's cells form a partition
exactly when the partition is binary (`compl_isPartition_iff`); complement probabilities sum
to one less than the number of cells and form a distribution exactly for two cells
(`sum_compl_prob`, `sum_compl_prob_eq_one_iff`); the binary partition of a proposition and
its negation is the coarsest coarsening preserving it, which is what `Setoid.Decides` says,
and a proposition and its negation carry the same partition (`Setoid.polar_compl`); an
attribute is negative with respect to a partition when its complement is a cell and its polar
question properly coarsens the partition (`IsNegativeAttribute`); and partition-relative
expected utility is the law of total expectation, a coarsening's cell terms regrouping the
finer partition's (`eu_eq_partitionEU`, `partitionEU_congr`). The paper's claim that
re-coverings which neither coarsen nor refine fail compositionality, and the
conditional-independence result of [johnson-1986] it cites, are not represented.

## TODO

The paper is not on file; page locators are transcribed from an earlier version of this
file and are UNVERIFIED.

## References

* [merin-1999]
* [johnson-1986]
-/

namespace Merin1999

open Core.DecisionTheory Core.DecisionTheory.DecisionProblem

/-! ### FACT 1: complement families -/

/-- FACT 1 ([merin-1999] p. 261): for a partition `F` of a
nonempty type, the complements of its cells form a partition iff `F`
has exactly two cells. -/
theorem compl_isPartition_iff {W : Type*} [Nonempty W] {F : Set (Set W)}
    (hF : Setoid.IsPartition F) :
    Setoid.IsPartition (compl '' F) ↔ F.encard = 2 := by
  have cover : ∀ a : W, ∃ B ∈ F, a ∈ B := λ a =>
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
      Set.nonempty_iff_ne_empty.mpr (λ h => hFc.1 (h ▸ hAc))
    obtain ⟨B, hB, hbB⟩ := cover b
    have hBA : B ≠ A := λ h => hb (h ▸ hbB)
    -- No third cell: its points would witness overlap of `Aᶜ` and `Bᶜ`.
    have hall : ∀ C ∈ F, C = A ∨ C = B := by
      intro C hC
      by_contra hne
      push Not at hne
      obtain ⟨hCA, hCB⟩ := hne
      obtain ⟨c, hc⟩ : Set.Nonempty C :=
        Set.nonempty_iff_ne_empty.mpr (λ h => hF.1 (h ▸ hC))
      have hcA : c ∈ Aᶜ := λ h => hCA (uniq hC hA hc h)
      have hcB : c ∈ Bᶜ := λ h => hCB (uniq hC hB hc h)
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

/-! ### FACT 3: complement probabilities -/

/-- FACT 3 ([merin-1999] p. 261): under a proper prior, the
probabilities of the complements of a partition's cells sum to `n − 1`,
`n` the number of cells. -/
theorem sum_compl_prob {W : Type*} [Fintype W] [DecidableEq W]
    (P : Finpartition (Finset.univ : Finset W)) (prior : W → ℚ)
    (hsum : Finset.univ.sum prior = 1) :
    P.parts.sum (λ c => (Finset.univ \ c).sum prior) =
      (P.parts.card : ℚ) - 1 := by
  have hpart : P.parts.sum (λ c => c.sum prior) = 1 := by
    rw [← hsum]
    conv_rhs => rw [show (Finset.univ : Finset W) = P.parts.biUnion id
      from P.biUnion_parts.symm]
    rw [Finset.sum_biUnion P.supIndep.pairwiseDisjoint]
    simp only [id]
  have hsplit : ∀ c ∈ P.parts,
      (Finset.univ \ c).sum prior = 1 - c.sum prior := by
    intro c _
    have h := Finset.sum_sdiff (f := prior) (Finset.subset_univ c)
    rw [hsum] at h
    linarith
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hpart,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Merin's FACT 2 ([merin-1999] p. 261), summed form: the
complement probabilities form a probability distribution (sum to `1`)
iff the partition is binary. -/
theorem sum_compl_prob_eq_one_iff {W : Type*} [Fintype W] [DecidableEq W]
    (P : Finpartition (Finset.univ : Finset W)) (prior : W → ℚ)
    (hsum : Finset.univ.sum prior = 1) :
    P.parts.sum (λ c => (Finset.univ \ c).sum prior) = 1 ↔
      P.parts.card = 2 := by
  rw [sum_compl_prob P prior hsum]
  constructor
  · intro h
    have : (P.parts.card : ℚ) = 2 := by linarith
    exact_mod_cast this
  · intro h
    rw [h]
    norm_num

/-! ### Coarsening and negative attributes -/

/-- Q properly coarsens Q': Q is strictly coarser than Q' in the refinement order, which over
a finite domain is coarsening with strictly fewer cells ([merin-1999] p. 262 definition). -/
def IsProperCoarsening {M : Type*} (q q' : Setoid M) : Prop := q' < q

/-- `R` is a **negative attribute** with respect to `q` ([merin-1999] p. 263): the complement
of `R` is a cell of `q`, and the two-cell partition `{R, ¬R}` properly coarsens `q`. Negativity
is epistemic (partition-kinetic), not morphological. -/
def IsNegativeAttribute {M : Type*} (R : Set M) (q : Setoid M) : Prop :=
  (∃ w, q.cell w = Rᶜ) ∧ IsProperCoarsening (Setoid.polar R) q

/-! ### EU compositionality under coarsening -/

variable {M : Type*} {A : Type*}

/-- Expected utility computed via a partition: weight each cell's conditional EU by the
cell's probability (`EU_Q(a) = Σ_{c ∈ cells Q} P(c) · EU(a | c)`). -/
def partitionEU [Fintype M] [DecidableEq M] (dp : DecisionProblem ℚ M A) (q : Setoid M)
    [DecidableRel q] (a : A) : ℚ :=
  ∑ cell ∈ (Finpartition.ofSetoid q).parts, cell.sum dp.prior * condExpectedUtility dp cell a

/-- Cell probability times conditional EU is the raw weighted sum, for non-negative priors. -/
private theorem cellProb_mul_conditionalEU [DecidableEq M]
    (dp : DecisionProblem ℚ M A) (cell : Finset M) (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cell.sum dp.prior * condExpectedUtility dp cell a =
    cell.sum (λ w => dp.prior w * dp.utility w a) := by
  simp only [condExpectedUtility]
  by_cases htot : cell.sum dp.prior = 0
  · simp only [htot, ite_true, mul_zero]
    symm; apply Finset.sum_eq_zero; intro w hw
    have hle : dp.prior w ≤ cell.sum dp.prior :=
      Finset.single_le_sum (λ x _ => hprior x) hw
    have hzero : dp.prior w = 0 := le_antisymm (by linarith) (hprior w)
    simp [hzero]
  · simp only [htot, ite_false]
    rw [Finset.mul_sum]
    congr 1; ext w; field_simp

/-- Law of total expectation: the unconditional expected utility equals the
partition-relative EU, for any partition (non-negative priors). -/
theorem eu_eq_partitionEU [Fintype M] [DecidableEq M] (dp : DecisionProblem ℚ M A) (a : A)
    (q : Setoid M) [DecidableRel q] (hprior : ∀ w, dp.prior w ≥ 0) :
    expectedUtility dp a = partitionEU dp q a := by
  simp only [expectedUtility, partitionEU]
  conv_lhs => rw [← (Finpartition.ofSetoid q).biUnion_parts]
  rw [Finset.sum_biUnion (Finpartition.ofSetoid q).supIndep.pairwiseDisjoint]
  exact Finset.sum_congr rfl (λ cell _ => (cellProb_mul_conditionalEU dp cell a hprior).symm)

/-- Partition-relative EU is partition-independent: any two partitions compute the
unconditional EU. [merin-1999] p. 264 is the coarsening instance; the paper's FACT 5, that
non-coarsening re-coverings *fail* term-by-term re-usability, is not formalized. -/
theorem partitionEU_congr [Fintype M] [DecidableEq M] (dp : DecisionProblem ℚ M A)
    (q q' : Setoid M) [DecidableRel q] [DecidableRel q'] (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionEU dp q a = partitionEU dp q' a :=
  (eu_eq_partitionEU dp a q hprior).symm.trans (eu_eq_partitionEU dp a q' hprior)

end Merin1999

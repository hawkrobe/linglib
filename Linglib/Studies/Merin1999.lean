import Linglib.Semantics.Questions.Partition.Lattice
import Linglib.Semantics.Questions.Partition.Cells
import Linglib.Semantics.Questions.DecisionTheory
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp

/-!
# Merin (1999) — Why *Not* Speak Notspeak
[merin-1999-notspeak]

[merin-1999-notspeak] "Negative Attributes, Partitions, and Rational
Decisions" gives a decision-theoretic rationale for attribute spaces
being partitions and a purely epistemic, syntax-independent
characterization of negative attributes as proper coarsenings.

Formalized:

- **FACT 1** (p. 261): the complements of a partition's cells form a
  partition iff the partition is binary (`compl_isPartition_iff`).
- **FACT 3** (p. 261): complement probabilities sum to `n − 1`
  (`sum_compl_prob`); they form a distribution iff `n = 2`
  (`sum_compl_prob_eq_one_iff`, Merin's FACT 2).
- **Coarsening** (p. 262): `IsProperCoarsening`; negation-induced binary
  partitions (`binaryPartition`, `complement_same_partition`).
- **FACT 4** (p. 263): `{P, ¬P}` is the coarsest `P`-preserving
  coarsening (`binaryPartition_coarsens`).
- **Negative attributes** (p. 263): `R` is negative w.r.t. partition `F`
  iff `{R, Q}` properly coarsens `F` for some cell `Q ∈ F`
  (`IsNegativeAttribute`).
- **EU compositionality under coarsening** (p. 264): partition-relative
  expected utility is the law of total expectation
  (`eu_eq_partitionEU`), and a coarsening's cell terms regroup the finer
  partition's terms (`partitionEU_coarsening_regroup`).

Not formalized: FACT 5 (pp. 264–265), that re-coverings which neither
coarsen nor refine *fail* compositionality (an existence claim over
discrete measures), and the [johnson-1986] conditional-independence
result motivating binary partitions in epistemic kinetics (§8, cited by
Merin, not proved there).
-/

namespace Merin1999

open QUD Core.DecisionTheory

/-! ### FACT 1: complement families -/

/-- FACT 1 ([merin-1999-notspeak] p. 261): for a partition `F` of a
nonempty type, the complements of its cells form a partition iff `F`
has exactly two cells. -/
theorem compl_isPartition_iff {W : Type*} [Nonempty W] {F : Set (Set W)}
    (hF : Setoid.IsPartition F) :
    Setoid.IsPartition (compl '' F) ↔ F.encard = 2 := by
  have cover : ∀ a : W, ∃ B ∈ F, a ∈ B := fun a =>
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
      Set.nonempty_iff_ne_empty.mpr (fun h => hFc.1 (h ▸ hAc))
    obtain ⟨B, hB, hbB⟩ := cover b
    have hBA : B ≠ A := fun h => hb (h ▸ hbB)
    -- No third cell: its points would witness overlap of `Aᶜ` and `Bᶜ`.
    have hall : ∀ C ∈ F, C = A ∨ C = B := by
      intro C hC
      by_contra hne
      push Not at hne
      obtain ⟨hCA, hCB⟩ := hne
      obtain ⟨c, hc⟩ : Set.Nonempty C :=
        Set.nonempty_iff_ne_empty.mpr (fun h => hF.1 (h ▸ hC))
      have hcA : c ∈ Aᶜ := fun h => hCA (uniq hC hA hc h)
      have hcB : c ∈ Bᶜ := fun h => hCB (uniq hC hB hc h)
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

/-- FACT 3 ([merin-1999-notspeak] p. 261): under a proper prior, the
probabilities of the complements of a partition's cells sum to `n − 1`,
`n` the number of cells. -/
theorem sum_compl_prob {W : Type*} [Fintype W] [DecidableEq W]
    (P : Finpartition (Finset.univ : Finset W)) (prior : W → ℚ)
    (hsum : Finset.univ.sum prior = 1) :
    P.parts.sum (fun c => (Finset.univ \ c).sum prior) =
      (P.parts.card : ℚ) - 1 := by
  have hpart : P.parts.sum (fun c => c.sum prior) = 1 := by
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

/-- Merin's FACT 2 ([merin-1999-notspeak] p. 261), summed form: the
complement probabilities form a probability distribution (sum to `1`)
iff the partition is binary. -/
theorem sum_compl_prob_eq_one_iff {W : Type*} [Fintype W] [DecidableEq W]
    (P : Finpartition (Finset.univ : Finset W)) (prior : W → ℚ)
    (hsum : Finset.univ.sum prior = 1) :
    P.parts.sum (fun c => (Finset.univ \ c).sum prior) = 1 ↔
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

/-- Binary partition from a Boolean predicate: two elements are
equivalent iff the predicate agrees on both. Negation-induced
repartitioning yields exactly these ([merin-1999-notspeak] §8). -/
abbrev binaryPartition {M : Type*} (p : M → Bool) : QUD M := ofProject p

/-- Complement predicates induce the same binary partition: a
proposition and its negation carry the same information. -/
theorem complement_same_partition {M : Type*} (p : M → Bool) (w v : M) :
    (binaryPartition p).sameAnswer w v =
    (binaryPartition (fun m => !p m)).sameAnswer w v := by
  simp only [ofProject_sameAnswer]
  cases p w <;> cases p v <;> rfl

/-- Q properly coarsens Q' over a finite domain: Q coarsens Q' with
strictly fewer cells ([merin-1999-notspeak] p. 262 definition). -/
def IsProperCoarsening {M : Type*} [DecidableEq M]
    (q q' : QUD M) (elements : List M) : Prop :=
  q.coarsens q' ∧ q.numCells elements < q'.numCells elements

/-- FACT 4 ([merin-1999-notspeak] p. 263): `{P, ¬P}` is the *coarsest*
`P`-preserving coarsening. Any partition whose cells respect `P` — in
particular any `P`-preserving coarsening of a given partition — is
refined by the binary partition of `P`. -/
theorem binaryPartition_coarsens {M : Type*} (q : QUD M) (p : M → Bool)
    (h : ∀ w v, q.sameAnswer w v = true → p w = p v) :
    (binaryPartition p).coarsens q := by
  intro w v hq
  simp only [ofProject_sameAnswer, beq_iff_eq]
  exact h w v hq

/-- `R` is a **negative attribute** with respect to `q`
([merin-1999-notspeak] p. 263): the complement of `R` is a cell of `q`,
and the two-cell partition `{R, ¬R}` properly coarsens `q`. Negativity
is epistemic (partition-kinetic), not morphological. -/
def IsNegativeAttribute {M : Type*} [DecidableEq M] (R : M → Bool)
    (q : QUD M) (elements : List M) : Prop :=
  (∃ w, ∀ v, q.sameAnswer w v = true ↔ R v = false) ∧
  IsProperCoarsening (binaryPartition R) q elements

/-! ### EU compositionality under coarsening -/

variable {M : Type*} {A : Type*}

/-- Expected utility computed via a partition: weight each cell's
conditional EU by the cell's probability
(`EU_Q(a) = Σ_{c ∈ cells Q} P(c) · EU(a | c)`). -/
def partitionEU [Fintype M] [DecidableEq M]
    (dp : DecisionProblem M A) (q : QUD M) (a : A) : ℚ :=
  (q.toCellsFinset Finset.univ).sum (fun cell =>
    cell.sum dp.prior * conditionalEU dp cell a)

/-- Cell probability times conditional EU is the raw weighted sum, for
non-negative priors. -/
private theorem cellProb_mul_conditionalEU [DecidableEq M]
    (dp : DecisionProblem M A) (cell : Finset M) (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cell.sum dp.prior * conditionalEU dp cell a =
    cell.sum (fun w => dp.prior w * dp.utility w a) := by
  simp only [conditionalEU]
  by_cases htot : cell.sum dp.prior = 0
  · simp only [htot, ite_true, mul_zero]
    symm; apply Finset.sum_eq_zero; intro w hw
    have hle : dp.prior w ≤ cell.sum dp.prior :=
      Finset.single_le_sum (fun x _ => hprior x) hw
    have hzero : dp.prior w = 0 := le_antisymm (by linarith) (hprior w)
    simp [hzero]
  · simp only [htot, ite_false]
    rw [Finset.mul_sum]
    congr 1; ext w; field_simp

/-- Law of total expectation: the unconditional expected utility equals
the partition-relative EU, for any partition (non-negative priors). -/
theorem eu_eq_partitionEU [Fintype M] [DecidableEq M]
    (dp : DecisionProblem M A) (a : A) (q : QUD M)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    expectedUtility dp a = partitionEU dp q a := by
  simp only [expectedUtility, partitionEU]
  conv_lhs => rw [show (Finset.univ : Finset M) =
    (q.toCellsFinset Finset.univ).biUnion id
    from (toCellsFinset_covers q Finset.univ).symm]
  rw [Finset.sum_biUnion (toCellsFinset_pairwiseDisjoint q Finset.univ)]
  exact Finset.sum_congr rfl (fun cell _ =>
    (cellProb_mul_conditionalEU dp cell a hprior).symm)

/-- Partition-relative EU is partition-independent: any two partitions
compute the unconditional EU. [merin-1999-notspeak] p. 264 is the
coarsening instance; the paper's FACT 5 — that non-coarsening
re-coverings *fail* term-by-term re-usability — is not formalized. -/
theorem partitionEU_congr [Fintype M] [DecidableEq M]
    (dp : DecisionProblem M A) (q q' : QUD M) (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionEU dp q a = partitionEU dp q' a :=
  (eu_eq_partitionEU dp a q hprior).symm.trans (eu_eq_partitionEU dp a q' hprior)

/-- EU compositionality under coarsening ([merin-1999-notspeak] p. 264):
each coarse cell's term is the sum of the terms of the fine cells it
groups, so a coarsening re-uses the finer partition's computations. -/
theorem partitionEU_coarsening_regroup [Fintype M] [DecidableEq M]
    (dp : DecisionProblem M A) {q q' : QUD M} (a : A)
    (hcoarse : q'.coarsens q)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionEU dp q' a =
      (q'.toCellsFinset Finset.univ).sum (fun c' =>
        ((q.toCellsFinset Finset.univ).filter (· ⊆ c')).sum (fun c =>
          c.sum dp.prior * conditionalEU dp c a)) := by
  unfold partitionEU
  refine Finset.sum_congr rfl (fun c' hc' => ?_)
  rw [cellProb_mul_conditionalEU dp c' a hprior]
  conv_lhs => rw [show c' = ((q.toCellsFinset Finset.univ).filter (· ⊆ c')).biUnion id
    from coarse_eq_biUnion_fine q q' Finset.univ hcoarse c' hc']
  rw [Finset.sum_biUnion (fine_cells_in_coarse_pairwiseDisjoint q Finset.univ c')]
  exact Finset.sum_congr rfl (fun c _ =>
    (cellProb_mul_conditionalEU dp c a hprior).symm)

end Merin1999

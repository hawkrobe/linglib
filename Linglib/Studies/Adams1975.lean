module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.TFAE

/-!
# Adams (1975): The Logic of Conditionals: An Application of Probability to Deductive Logic

Adams asks when an inference is probabilistically sound: when making the premises certain enough
makes the conclusion as certain as one likes. For factual formulas, whose probability is the
probability that they are true, the answer is classical. Such an inference is probabilistically
sound exactly when it is logically valid, and then the conclusion's uncertainty, its probability
of being false, is at most the sum of the premises' uncertainties. The bound cannot be improved:
in a lottery, many premises that are each nearly certain jointly entail a conclusion that is
certainly false.

## Main results

* `tfae_pEntails`: for factual formulas, logical consequence, p-entailment, the uncertainty bound
  under every probability, and the preservation of certainty coincide.
* `uncertainty_le_sum`: the uncertainty of a logical consequence is at most the sum of the
  premises' uncertainties.
* `lottery_attains_bound`: in a uniform lottery the bound holds with equality.

## Implementation notes

* Possible states of affairs form a measurable space, a factual formula is the measurable set of
  states where it is true, and a probability-assignment is a probability measure, after Adams's
  assumption that a proposition's probability is the measure of the states in which it is true.
  His assignments are finitely additive on formulas; over finitely many atoms these are the
  measures on truth assignments, and beyond that countable additivity is an added assumption.
* Uncertainty, probability of falsity, is stated directly as `μ Aᶜ` rather than defined.
* Only factual formulas are treated, so every assignment is proper and no premise or conclusion
  is conditional.

## TODO

* The conditional extension: `A ⇒ B` with probability `μ[B|A]`, proper assignments, and the
  inferences where p-entailment and the logical consequence of material counterparts part ways,
  as `A ⊃ B` entails the material counterpart of `A ⇒ B` but does not p-entail it.

## References

* [E. W. Adams, *The Logic of Conditionals: An Application of Probability to Deductive
  Logic*][adams-1975]
-/

@[expose] public section

namespace Adams1975

open MeasureTheory ENNReal ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {s : Finset ι} {A : ι → Set Ω} {B : Set Ω}

/-- The premises `A i`, `i ∈ s`, p-entail `B` when, however probable `B` must be, making every
premise probable enough makes it so (Definition 2, for factual formulas). -/
def PEntails (s : Finset ι) (A : ι → Set Ω) (B : Set Ω) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ i ∈ s, 1 - δ ≤ μ (A i)) → 1 - ε ≤ μ B

/-- The uncertainty of a logical consequence is at most the sum of the premises' uncertainties,
the rule of Section I.1 that Theorem 3.1 generalizes. -/
theorem uncertainty_le_sum (h : ⋂ i ∈ s, A i ⊆ B) (μ : Measure Ω) :
    μ Bᶜ ≤ ∑ i ∈ s, μ (A i)ᶜ :=
  calc μ Bᶜ ≤ μ (⋃ i ∈ s, (A i)ᶜ) := measure_mono fun w hw ↦ by
        by_contra hw'
        simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hw'
        exact hw (h (Set.mem_iInter₂.mpr hw'))
    _ ≤ ∑ i ∈ s, μ (A i)ᶜ := measure_biUnion_finset_le s _

/-- A state where the premises hold and the conclusion fails gives a probability measure, its
point mass, that makes the premises certain and the conclusion certainly false. -/
theorem exists_dirac_of_not_subset (hB : MeasurableSet B) (h : ¬ ⋂ i ∈ s, A i ⊆ B) :
    ∃ w, (∀ i ∈ s, Measure.dirac w (A i) = 1) ∧ Measure.dirac w B = 0 := by
  obtain ⟨w, hw, hwB⟩ := Set.not_subset.mp h
  exact ⟨w, fun i hi ↦ Measure.dirac_apply_of_mem (Set.mem_iInter₂.mp hw i hi), by
    rw [Measure.dirac_apply' _ hB, Set.indicator_of_notMem hwB]⟩

/-- **Theorems 3.1, 3.3 and 3.4, for factual formulas.** Logical consequence, p-entailment, the
uncertainty bound under every probability, and the preservation of certainty coincide; for
factual premises 3.3 needs no consistency assumption. -/
theorem tfae_pEntails (hA : ∀ i ∈ s, MeasurableSet (A i)) (hB : MeasurableSet B) :
    [⋂ i ∈ s, A i ⊆ B,
      PEntails s A B,
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → μ Bᶜ ≤ ∑ i ∈ s, μ (A i)ᶜ,
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → (∀ i ∈ s, μ (A i) = 1) → μ B = 1].TFAE := by
  tfae_have 1 → 3 := fun h μ _ ↦ uncertainty_le_sum h μ
  tfae_have 3 → 4 := fun h μ hμ h1 ↦ by
    have : μ Bᶜ = 0 := nonpos_iff_eq_zero.mp ((h μ hμ).trans_eq (Finset.sum_eq_zero fun i hi ↦ by
      rw [prob_compl_eq_one_sub (hA i hi), h1 i hi, tsub_self]))
    rwa [prob_compl_eq_zero_iff hB] at this
  tfae_have 4 → 1 := fun h ↦ by
    by_contra hn
    obtain ⟨w, h1, h0⟩ := exists_dirac_of_not_subset hB hn
    simp [h (Measure.dirac w) inferInstance h1] at h0
  tfae_have 3 → 2 := fun h ε hε ↦ by
    refine ⟨ε / (s.card + 1), ENNReal.div_pos hε.ne' (by simp), fun μ hμ hp ↦ ?_⟩
    have hu : ∀ i ∈ s, μ (A i)ᶜ ≤ ε / (s.card + 1) := fun i hi ↦ by
      rw [prob_compl_eq_one_sub (hA i hi)]
      exact tsub_le_iff_tsub_le.mp (hp i hi)
    have hsum : μ Bᶜ ≤ ε := (h μ hμ).trans <| (Finset.sum_le_sum hu).trans <| by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc (s.card : ℝ≥0∞) * (ε / (s.card + 1)) ≤ (s.card + 1) * (ε / (s.card + 1)) := by
            gcongr; exact le_self_add
        _ ≤ ε := ENNReal.mul_div_le
    rw [prob_compl_eq_one_sub hB] at hsum
    exact tsub_le_iff_tsub_le.mp hsum
  tfae_have 2 → 1 := fun h ↦ by
    by_contra hn
    obtain ⟨w, h1, h0⟩ := exists_dirac_of_not_subset hB hn
    obtain ⟨δ, -, hδ⟩ := h (1 / 2) (by norm_num)
    have := hδ (Measure.dirac w) inferInstance fun i hi ↦ (h1 i hi).symm ▸ tsub_le_self
    rw [h0, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at this
    exact absurd this (by norm_num)
  tfae_finish

/-- Where the premises do not p-entail the conclusion, premises as probable as one likes are
compatible with a conclusion as improbable as one likes (Theorem 3.2, for factual formulas). -/
theorem exists_of_not_pEntails (hA : ∀ i ∈ s, MeasurableSet (A i)) (hB : MeasurableSet B)
    (h : ¬ PEntails s A B) (ε : ℝ≥0∞) :
    ∃ μ : Measure Ω, IsProbabilityMeasure μ ∧ (∀ i ∈ s, 1 - ε ≤ μ (A i)) ∧ μ B ≤ ε := by
  obtain ⟨w, h1, h0⟩ := exists_dirac_of_not_subset hB (mt ((tfae_pEntails hA hB).out 1 2).mp h)
  exact ⟨Measure.dirac w, inferInstance, fun i hi ↦ by rw [h1 i hi]; exact tsub_le_self, by
    rw [h0]; exact zero_le⟩

/-- **The lottery.** Each of `n + 1` tickets loses with uncertainty `1 / (n + 1)`, yet that every
ticket loses is certainly false, so the uncertainty bound holds with equality. -/
theorem lottery_attains_bound (n : ℕ) :
    let μ := uniformOn (Set.univ : Set (Fin (n + 1)))
    μ (⋂ i ∈ Finset.univ, ({i}ᶜ : Set (Fin (n + 1))))ᶜ = 1 ∧
      ∑ i : Fin (n + 1), μ ({i}ᶜ)ᶜ = 1 := by
  refine ⟨by simp [Set.iUnion_of_singleton], ?_⟩
  simp [uniformOn_univ, ENNReal.mul_inv_cancel]

end Adams1975

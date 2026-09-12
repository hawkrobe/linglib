import Linglib.Pragmatics.RSA.Basic
import Mathlib.Probability.ConditionalProbability

/-!
# Lassiter and Goodman (2017): Adjectival Vagueness in a Bayesian Model of Interpretation

This file formalizes the free-variable Rational Speech Act model of [lassiter-goodman-2017] on
the RSA kernel pipeline. A positive-form gradable adjective compares a degree with a threshold
the semantics leaves open (`sem`); the pragmatic listener resolves the threshold jointly with
the state, threading each candidate assignment through a threshold-indexed literal listener and
speaker (`L0`, `S1`) and inverting the family against the product of the degree prior and the
threshold prior (`L1`). The threshold marginal of that posterior gives the metalinguistic
probability that an individual counts as tall, the posterior mass of thresholds below the
individual's height (`metalinguistic`), and borderline cases are those of intermediate
metalinguistic probability.

The sorites dissolves as in Edgington. Read materially, the inductive premises fail exactly
when the threshold falls in the gap between adjacent members, and the gap masses sum to the
mass of the whole range (`sum_gapMass`), so each can be small while their sum is near one;
Adams's theorem bounds the uncertainty of the conclusion of a valid argument by the summed
uncertainty of its premises (`adams`), and the sorites is valid (`sorites_uncertainty`).
Read by Adams's Thesis, each premise is a conditional probability of the threshold marginal
and is at most the material premise (`conditionalPremise_le`).

## Implementation notes

Degrees form a finite linear order so that the discrete pipeline applies; the paper's
continuous scale and normal prior enter only through its simulations, which are not stated.
The assignment of the paper's eq. 27 is the pair of thresholds for the adjective and its
antonym, and the threshold prior is a parameter rather than the paper's uniform prior, which
the model never uses beyond its being a prior.

## TODO

The free-variable reading of the inductive premise (the paper's eq. 44), the antonym symmetry
of the simulations, and the scalar-implicature warm-up of §3 are not stated.

## References

* [lassiter-goodman-2017]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace LassiterGoodman2017

/-- The utterances: the adjective, its antonym, and saying nothing. -/
inductive Utterance
  | tall | short | silent
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩
instance : Nonempty Utterance := ⟨.silent⟩

variable {D : Type*} [LinearOrder D] [MeasurableSpace D] [DiscreteMeasurableSpace D]

/-- The meaning of an utterance at a degree under an assignment of thresholds to the adjective
and its antonym (eqs. 22–23): *tall* holds above the first threshold, *short* below the second,
and silence everywhere. -/
def sem (θ : D × D) : Utterance → Set D
  | .tall => Set.Ioi θ.1
  | .short => Set.Iio θ.2
  | .silent => Set.univ

/-- The literal listener at an assignment (eq. 27): the degree prior conditioned on the truth
of the utterance. -/
noncomputable def L0 (μ : Measure D) (θ : D × D) : Kernel Utterance D :=
  literalListener μ λ u => (sem θ u).indicator 1

theorem L0_apply_singleton_ne_zero_iff (μ : Measure D) [IsFiniteMeasure μ] (θ : D × D)
    (u : Utterance) (d : D) : L0 μ θ u {d} ≠ 0 ↔ d ∈ sem θ u ∧ μ {d} ≠ 0 := by
  by_cases h : d ∈ sem θ u
  · rw [L0, literalListener_indicator_apply_singleton μ (sem θ) h]
    exact ⟨λ h' => ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      λ h' => mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [L0, literalListener_indicator_apply_singleton_of_notMem μ (sem θ) h]
    exact iff_of_false (λ h' => h' rfl) (λ h' => h h'.1)

section Model

variable [Fintype D]

/-- The speaker at an assignment (eq. 28): the family speaker over degrees and assignments at
rationality `α` with cost factors `cost`. -/
noncomputable def S1 (μ : Measure D) (α : ℝ) (cost : Utterance → ℝ≥0∞) :
    Kernel (D × (D × D)) Utterance :=
  familySpeaker (L0 μ) α cost

/-- The pragmatic listener (eq. 29): the family listener against the product of the degree
prior and the threshold prior. Its first marginal is the degree posterior (eq. 31), its second
the posterior over assignments (eq. 30). -/
noncomputable def L1 [Nonempty D] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure (D × D)) [IsProbabilityMeasure ν] (α : ℝ) (cost : Utterance → ℝ≥0∞) :
    Kernel Utterance (D × (D × D)) :=
  familyListener (L0 μ) α cost (μ.prod ν)

variable (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure (D × D)) (α : ℝ)
  (cost : Utterance → ℝ≥0∞)

/-- The speaker produces an utterance at a degree and assignment exactly when it is true there
and the degree has positive prior. -/
theorem S1_apply_singleton_ne_zero_iff (hα : 0 < α) (hc0 : ∀ u, cost u ≠ 0)
    (hctop : ∀ u, cost u ≠ ∞) (d : D) (θ : D × D) (u : Utterance) :
    S1 μ α cost (d, θ) {u} ≠ 0 ↔ d ∈ sem θ u ∧ μ {d} ≠ 0 := by
  rw [S1, familySpeaker_apply, ← L0_apply_singleton_ne_zero_iff μ θ u d]
  exact ⟨λ h h' => h (speaker_apply_singleton_eq_zero hα h'),
    speaker_apply_singleton_ne_zero hα.le hc0 hctop
      λ u' => literalListener_apply_le_one μ _ u' {d}⟩

/-- An utterance true at a degree of positive prior under an assignment of positive prior has
a positive marginal. -/
theorem comp_S1_ne_zero (hα : 0 < α) (hc0 : ∀ u, cost u ≠ 0) (hctop : ∀ u, cost u ≠ ∞)
    {u : Utterance} {d : D} {θ : D × D} (hd : μ {d} ≠ 0) (hθ : ν {θ} ≠ 0) (hu : d ∈ sem θ u) :
    (S1 μ α cost ∘ₘ μ.prod ν) {u} ≠ 0 :=
  comp_familySpeaker_ne_zero (w := d) (l := θ)
    (by rw [← Set.singleton_prod_singleton, Measure.prod_prod]; exact mul_ne_zero hd hθ)
    ((S1_apply_singleton_ne_zero_iff μ α cost hα hc0 hctop d θ u).mpr ⟨hu, hd⟩)

variable [Nonempty D] [IsProbabilityMeasure ν]

instance : IsMarkovKernel (L1 μ ν α cost) :=
  inferInstanceAs (IsMarkovKernel ((familySpeaker (L0 μ) α cost)†(μ.prod ν)))

/-- Truthfulness: the pragmatic listener puts positive mass on a degree and assignment exactly
when both have positive prior and the utterance is true at the degree under the assignment. -/
theorem L1_apply_singleton_ne_zero_iff (hα : 0 < α) (hc0 : ∀ u, cost u ≠ 0)
    (hctop : ∀ u, cost u ≠ ∞) {u : Utterance} (hu : (S1 μ α cost ∘ₘ μ.prod ν) {u} ≠ 0)
    (d : D) (θ : D × D) :
    L1 μ ν α cost u {(d, θ)} ≠ 0 ↔ μ {d} ≠ 0 ∧ ν {θ} ≠ 0 ∧ d ∈ sem θ u := by
  have hs := S1_apply_singleton_ne_zero_iff μ α cost hα hc0 hctop d θ u
  rw [S1, familySpeaker_apply] at hs
  rw [L1, familyListener_apply_singleton _ _ _ hu, ← Set.singleton_prod_singleton,
    Measure.prod_prod]
  simp only [ne_eq, ENNReal.div_eq_zero_iff, mul_eq_zero, not_or, measure_ne_top,
    not_false_eq_true, and_true] at hs ⊢
  rw [hs]
  tauto

/-- The posterior over the adjective's threshold (eq. 30): the marginal of the listener on the
first coordinate of the assignment. -/
noncomputable def thresholdPosterior (u : Utterance) : Measure D :=
  (L1 μ ν α cost u).snd.fst

instance (u : Utterance) : IsProbabilityMeasure (thresholdPosterior μ ν α cost u) := by
  unfold thresholdPosterior; infer_instance

/-- The metalinguistic probability that a degree counts as tall under a threshold measure
(eq. 32): the mass of thresholds below it. -/
noncomputable def metalinguistic (ρ : Measure D) (d : D) : ℝ≥0∞ := ρ (Set.Iio d)

/-- The metalinguistic probability marginalizes the joint posterior over the degree and the
antonym's threshold. -/
theorem metalinguistic_thresholdPosterior (u : Utterance) (d : D) :
    metalinguistic (thresholdPosterior μ ν α cost u) d
      = L1 μ ν α cost u {p | p.2.1 < d} := by
  rw [metalinguistic, thresholdPosterior, Measure.fst_apply .of_discrete,
    Measure.snd_apply .of_discrete]
  rfl

/-- A borderline case: a degree of intermediate metalinguistic probability. -/
def Borderline (ρ : Measure D) (d : D) : Prop :=
  0 < metalinguistic ρ d ∧ metalinguistic ρ d < 1

end Model

/-! ### The sorites -/

section Sorites

variable (ρ : Measure D)

/-- The failure probability of a material inductive premise (eq. 37): the threshold falls
between two adjacent members. -/
noncomputable def gapMass (a b : D) : ℝ≥0∞ := ρ (Set.Ico a b)

/-- Along a monotone sequence the gap masses sum to the mass of the whole range. -/
theorem sum_gapMass (x : ℕ → D) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n, gapMass ρ (x i) (x (i + 1)) = gapMass ρ (x 0) (x n) := by
  induction n with
  | zero => simp [gapMass]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, gapMass, gapMass, gapMass,
      ← measure_union Set.Ico_disjoint_Ico_same .of_discrete,
      Set.Ico_union_Ico_eq_Ico (hx (Nat.zero_le n)) (hx n.le_succ)]

/-- Adams's theorem: the uncertainty of the conclusion of a valid argument is at most the
summed uncertainty of its premises. -/
theorem adams {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i)) {C : Set Ω}
    (hC : ⋂ i ∈ s, A i ⊆ C) : 1 - μ C ≤ ∑ i ∈ s, (1 - μ (A i)) := by
  calc 1 - μ C ≤ 1 - μ (⋂ i ∈ s, A i) := tsub_le_tsub_left (measure_mono hC) 1
    _ = μ (⋂ i ∈ s, A i)ᶜ := (prob_compl_eq_one_sub (.biInter s.countable_toSet hA)).symm
    _ = μ (⋃ i ∈ s, (A i)ᶜ) := by rw [Set.compl_iInter₂]
    _ ≤ ∑ i ∈ s, μ (A i)ᶜ := measure_biUnion_finset_le s _
    _ = ∑ i ∈ s, (1 - μ (A i)) :=
      Finset.sum_congr rfl λ i hi => prob_compl_eq_one_sub (hA i hi)

omit [MeasurableSpace D] [DiscreteMeasurableSpace D] in
/-- The material sorites is valid: if the top member is tall and no gap holds the threshold,
the bottom member is tall. -/
theorem sorites_valid (x : ℕ → D) (n : ℕ) {θ : D} (hθ : θ < x n)
    (hgap : ∀ i ∈ Finset.range n, θ ∉ Set.Ico (x i) (x (i + 1))) : θ < x 0 := by
  induction n with
  | zero => exact hθ
  | succ n ih =>
    exact ih (lt_of_not_ge λ h => hgap n (Finset.mem_range.mpr n.lt_succ_self) ⟨h, hθ⟩)
      λ i hi => hgap i (Finset.range_mono n.le_succ hi)

variable [IsProbabilityMeasure ρ]

/-- The uncertainty of the sorites conclusion is bounded by the uncertainty that the top member
is tall plus the summed gap masses, which is the mass of the whole range. -/
theorem sorites_uncertainty (x : ℕ → D) (hx : Monotone x) (n : ℕ) :
    1 - metalinguistic ρ (x 0) ≤ (1 - metalinguistic ρ (x n)) + gapMass ρ (x 0) (x n) := by
  have h := adams ρ (Finset.range (n + 1))
    (λ i => if i < n then (Set.Ico (x i) (x (i + 1)))ᶜ else Set.Iio (x n))
    (λ _ _ => .of_discrete) (C := Set.Iio (x 0)) ?_
  · rw [Finset.sum_range_succ, if_neg (lt_irrefl n),
      Finset.sum_congr rfl (λ i hi => by rw [if_pos (Finset.mem_range.mp hi)]),
      add_comm] at h
    simp only [prob_compl_eq_one_sub (MeasurableSet.of_discrete),
      ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one] at h
    rwa [← sum_gapMass ρ x hx]
  · intro θ hθ
    rw [Set.mem_iInter₂] at hθ
    have htop := hθ n (Finset.mem_range.mpr n.lt_succ_self)
    rw [if_neg (lt_irrefl n)] at htop
    exact sorites_valid x n htop λ i hi => by
      have := hθ i (Finset.range_mono n.le_succ hi)
      rwa [if_pos (Finset.mem_range.mp hi)] at this

/-- Under Adams's Thesis (eq. 40) an inductive premise is the conditional probability that
the lower member is tall given that the upper one is, which is at most the material premise,
the probability that the threshold avoids the gap. -/
theorem conditionalPremise_le {a b : D} (hab : a ≤ b) :
    ρ[Set.Iio a | Set.Iio b] ≤ ρ (Set.Ico a b)ᶜ := by
  rw [cond_apply .of_discrete, Set.Iio_inter_Iio, min_eq_right hab,
    prob_compl_eq_one_sub .of_discrete]
  have hsplit : ρ (Set.Iio b) = ρ (Set.Iio a) + ρ (Set.Ico a b) := by
    rw [← measure_union ((Set.Iio_disjoint_Ici le_rfl).mono_right Set.Ico_subset_Ici_self)
      .of_discrete, Set.Iio_union_Ico_eq_Iio hab]
  rcases eq_or_ne (ρ (Set.Iio b)) 0 with h0 | h0
  · rw [measure_mono_null (Set.Iio_subset_Iio hab) h0, mul_zero]
    exact zero_le
  rw [ENNReal.inv_mul_le_iff h0 (measure_ne_top _ _),
    ENNReal.mul_sub (λ _ _ => measure_ne_top _ _), mul_one, hsplit]
  calc ρ (Set.Iio a) = ρ (Set.Iio a) + ρ (Set.Ico a b) - ρ (Set.Ico a b) :=
        (ENNReal.add_sub_cancel_right (measure_ne_top _ _)).symm
    _ ≤ ρ (Set.Iio a) + ρ (Set.Ico a b) - (ρ (Set.Iio a) + ρ (Set.Ico a b)) * ρ (Set.Ico a b) :=
        tsub_le_tsub_left (mul_le_of_le_one_left zero_le (hsplit ▸ prob_le_one)) _

end Sorites

end LassiterGoodman2017

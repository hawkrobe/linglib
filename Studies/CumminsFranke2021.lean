module

public import Linglib.Pragmatics.DecisionTheoretic.Basic
public import Linglib.Core.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Cummins and Franke (2021): Rational Interpretation of Numerical Quantity in Argumentative Contexts

Cummins and Franke measure the argumentative strength of a numerical utterance toward a
speaker's goal, after Merin, as a log Bayes factor: once on the utterance's truth conditions
and once on its felicitous assertability, which accounts for the implicatures a hearer may
draw. In their conference example the goal is that more than 120 people attend, attendees are
those who registered, registrations are uniform on [0, 200], and the speaker chooses between
*more than 100* and *more than 110*. Semantically the stronger utterance is the stronger
argument, but a hearer who reads *more than 110* as implicating *not more than 120* finds that
reading incompatible with the goal, so pragmatically the utterance is only weak evidence and
the order reverses.

We derive the semantic ordering from the general fact that shedding worlds where the goal
fails only strengthens an argument. Both implicatures hold wherever the goal fails, so the
pragmatic Bayes factor is the semantic one discounted by the enrichment rate times the
probability, given success and the utterance, that the implicature fails: five eighths for
*more than 100* and one for *more than 110*. At rate zero the two measures coincide. For any
implicature of *more than 100* at or above the goal the reversal is an inequality in the
rate; for the paper's *not more than 150* the order reverses exactly when the hearer enriches
more than eight times in eleven, and the paper's printed pragmatic strengths follow at its
rate of nine in ten. Only this illustration, which the paper calls unrealistic, is
formalized: its high-framing examples, its rules for a sceptical hearer and its corpus study
are not.

## Implementation notes

* Registrations are binned into twenty bands of width ten under a counting prior. Every
  threshold in the illustration is a band boundary, so its uniform prior is represented
  exactly; the alternative implicature *not more than 125* that the paper mentions is not.
* For *more than 110* the paper prints log 11, the Bayes factor of *more than 100* toward the
  goal *more than 110*. Its own pragmatic calculation gives *more than 110* probability 1/12
  given failure, so toward the stated goal the factor is 12, which the rate-zero case
  recovers. The ordering is unaffected.
* Strengths are natural logarithms; the paper prints base-ten decimals, and a change of base
  preserves the sign, order and ratios of strengths.

## References

* [cummins-franke-2021]
* [merin-1999-relevance]
-/

@[expose] public section

namespace CumminsFranke2021

open DTS MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

/-! ### The conference -/

/-- Band `k` holds the registration totals in `(10k, 10(k+1)]`. -/
abbrev Band := Fin 20

/-- The extension of *more than n* for a threshold `n` that is a multiple of ten. -/
def moreThan (n : ℕ) : Set Band := {k | n ≤ 10 * (k : ℕ)}

instance (n : ℕ) : DecidablePred (· ∈ moreThan n) := fun k ↦
  inferInstanceAs (Decidable (n ≤ 10 * (k : ℕ)))

theorem moreThan_antitone : Antitone moreThan := fun _ _ h _ hk ↦ h.trans hk

/-- The conference succeeds iff more than 120 people register, and so attend, under the
counting prior. -/
noncomputable abbrev success : Context Band := ⟨moreThan 120, .of_discrete, .count⟩

private theorem ncard_eq (s : Set Band) [DecidablePred (· ∈ s)] (n : ℕ)
    (h : s.toFinset.card = n := by decide) : s.ncard = n :=
  (Set.ncard_eq_toFinset_card' s).trans h

/-! ### Truth conditions -/

/-- Success is at least as probable given *more than 110* as given *more than 100*, since
the bands that *more than 110* sheds are all failures. -/
theorem uniformOn_moreThan100_le_moreThan110 :
    uniformOn (moreThan 100) (moreThan 120) ≤ uniformOn (moreThan 110) (moreThan 120) :=
  cond_le_cond_of_subset _ .of_discrete .of_discrete (moreThan_antitone (by norm_num))
    (Set.inter_subset_left.trans (moreThan_antitone (by norm_num)))

/-- Hence *more than 110* is semantically the stronger argument for success. -/
theorem bayesFactor_moreThan100_lt_moreThan110 :
    bayesFactor success (moreThan 100) < bayesFactor success (moreThan 110) :=
  bayesFactor_lt_of_subset success .of_discrete (moreThan_antitone (by norm_num))
    (Set.inter_subset_left.trans (moreThan_antitone (by norm_num)))
    (Measure.count_ne_zero_iff.mpr ⟨12, by decide⟩)
    (Measure.count_ne_zero_iff.mpr ⟨10, by decide⟩)

theorem toReal_bayesFactor_moreThan100 : (bayesFactor success (moreThan 100)).toReal = 6 := by
  rw [toReal_bayesFactor_count, ncard_eq (moreThan 120 ∩ moreThan 100) 8,
    ncard_eq (moreThan 120) 8, ncard_eq ((moreThan 120)ᶜ ∩ moreThan 100) 2,
    ncard_eq (moreThan 120)ᶜ 12]
  norm_num

theorem toReal_bayesFactor_moreThan110 : (bayesFactor success (moreThan 110)).toReal = 12 := by
  rw [toReal_bayesFactor_count, ncard_eq (moreThan 120 ∩ moreThan 110) 8,
    ncard_eq (moreThan 120) 8, ncard_eq ((moreThan 120)ᶜ ∩ moreThan 110) 1,
    ncard_eq (moreThan 120)ᶜ 12]
  norm_num

/-- The paper's log 6 for *more than 100*. -/
theorem relevance_moreThan100 : relevance success (moreThan 100) = Real.log 6 :=
  congrArg Real.log toReal_bayesFactor_moreThan100

/-- Toward the stated goal *more than 110* has strength log 12, where the paper prints
log 11. -/
theorem relevance_moreThan110 : relevance success (moreThan 110) = Real.log 12 :=
  congrArg Real.log toReal_bayesFactor_moreThan110

/-- The paper's log 11 is the strength of *more than 100* toward the goal *more than 110*. -/
theorem relevance_moreThan100_toward110 :
    relevance ⟨moreThan 110, .of_discrete, .count⟩ (moreThan 100) = Real.log 11 := by
  rw [relevance_count, ncard_eq (moreThan 110 ∩ moreThan 100) 9, ncard_eq (moreThan 110) 9,
    ncard_eq ((moreThan 110)ᶜ ∩ moreThan 100) 1, ncard_eq (moreThan 110)ᶜ 11]
  norm_num

/-! ### Assertability

Assertability is stochastic: with probability `ρ` the hearer gives the utterance a pragmatic
interpretation, enriching it with its scalar implicature (*more than 100* to *not more than
150*, *more than 110* to *not more than 120*), and otherwise a semantic one, so the utterance
is felicitously assertable iff it is true on the interpretation drawn. The joint of
registrations and interpretations is the product of the counting prior with the hearer's
coin. -/

/-- How the hearer resolves the utterance. -/
inductive Interpretation where
  | pragmatic | semantic
  deriving DecidableEq, Fintype

instance : MeasurableSpace Interpretation := ⊤

/-- The hearer interprets pragmatically with probability `ρ` and semantically otherwise. -/
noncomputable abbrev hearer (ρ : I) : Measure Interpretation := Ber(.pragmatic, .semantic, ρ)

/-- The readings of *more than n* whose enrichment is *not more than cap*. -/
def reading (n cap : ℕ) : Interpretation → Set Band
  | .pragmatic => moreThan n \ moreThan cap
  | .semantic => moreThan n

/-- The assertability model pairs registrations with the hearer's interpretation under the
counting prior and the hearer's coin, and lifts the goal along the registration. -/
noncomputable abbrev assertability (ρ : I) : Context (Band × Interpretation) :=
  ⟨Prod.fst ⁻¹' moreThan 120, measurable_fst .of_discrete, Measure.count.prod (hearer ρ)⟩

/-- *more than n* is felicitously assertable iff it is true on the interpretation drawn. -/
def assertable (n cap : ℕ) : Set (Band × Interpretation) := {p | p.1 ∈ reading n cap p.2}

/-- Given the registration band, the probability that *more than n* is assertable is the
paper's mixture of its readings' proportions. -/
theorem real_cond_assertable (ρ : I) (s : Set Band) (n cap : ℕ) :
    ((Measure.count.prod (hearer ρ))[|Prod.fst ⁻¹' s]).real (assertable n cap) =
      (uniformOn s).real (moreThan n \ moreThan cap) * ρ +
        (uniformOn s).real (moreThan n) * (1 - ρ) := by
  rw [cond_prod_preimage_fst, assertable, Measure.prod_real_fibers _ _ fun _ ↦ .of_discrete,
    Fintype.sum_eq_add .pragmatic .semantic (by decide) (by rintro (_ | _) <;> simp)]
  simp [reading, uniformOn]

/-- Given failure, *more than n* is as probable to be assertable as to be true, when its
implicature holds wherever the conference fails. -/
theorem real_assertable_of_failure (ρ : I) (n : ℕ) {cap : ℕ} (hcap : 120 ≤ cap) :
    ((assertability ρ).prior[|(assertability ρ).topicᶜ]).real (assertable n cap) =
      (uniformOn (moreThan 120)ᶜ).real (moreThan n) := by
  have h : (moreThan 120)ᶜ ∩ (moreThan n \ moreThan cap) = (moreThan 120)ᶜ ∩ moreThan n :=
    Set.inter_congr_left (fun _ hk ↦ ⟨hk.2, fun hc ↦ hk.1 (moreThan_antitone hcap hc)⟩)
      fun _ hk ↦ hk.2.1
  rw [← Set.preimage_compl, real_cond_assertable, uniformOn_real_apply, uniformOn_real_apply, h]
  ring

/-- Given success, the probability that *more than n* is assertable is its probability of
truth, discounted by the enrichment rate times the probability, given success and the
utterance, that its implicature fails. -/
theorem real_assertable_of_success (ρ : I) (n cap : ℕ) :
    ((assertability ρ).prior[|(assertability ρ).topic]).real (assertable n cap) =
      (uniformOn (moreThan 120)).real (moreThan n) *
        (1 - ρ * (uniformOn (moreThan 120 ∩ moreThan n)).real (moreThan cap)) := by
  have hdiff := measureReal_sdiff_add_inter (μ := uniformOn (moreThan 120)) (s := moreThan n)
    (t := moreThan cap) .of_discrete
  have hinter : (uniformOn (moreThan 120)).real (moreThan n ∩ moreThan cap) =
      (uniformOn (moreThan 120 ∩ moreThan n)).real (moreThan cap) *
        (uniformOn (moreThan 120)).real (moreThan n) := by
    simp only [measureReal_def, uniformOn_inter (Set.toFinite _), ENNReal.toReal_mul]
  rw [real_cond_assertable]
  linear_combination (ρ : ℝ) * hdiff - (ρ : ℝ) * hinter

/-- The pragmatic Bayes factor of *more than n* is the semantic one discounted by the enrichment
rate times the probability, given success and the utterance, that its implicature fails, when
the implicature holds wherever the conference fails. -/
theorem toReal_bayesFactor_assertable (ρ : I) (n : ℕ) {cap : ℕ} (hcap : 120 ≤ cap) :
    (bayesFactor (assertability ρ) (assertable n cap)).toReal =
      (bayesFactor success (moreThan n)).toReal *
        (1 - ρ * (uniformOn (moreThan 120 ∩ moreThan n)).real (moreThan cap)) := by
  rw [toReal_bayesFactor, toReal_bayesFactor, real_assertable_of_success,
    real_assertable_of_failure ρ n hcap]
  exact mul_div_right_comm _ _ _

/-- At enrichment rate zero the pragmatic measure is the semantic one. -/
theorem bayesFactor_assertability_zero (n cap : ℕ) :
    bayesFactor (assertability 0) (assertable n cap) = bayesFactor success (moreThan n) := by
  have h (s : Set Band) : (Measure.count.prod (hearer 0))[|Prod.fst ⁻¹' s] (assertable n cap) =
      uniformOn s (moreThan n) := by
    rw [← measureReal_eq_measureReal_iff, real_cond_assertable]
    simp
  rw [bayesFactor_def, bayesFactor_def, ← Set.preimage_compl, h, h]
  rfl

theorem toReal_bayesFactor_assertable_moreThan100 (ρ : I) {cap : ℕ} (hcap : 120 ≤ cap) :
    (bayesFactor (assertability ρ) (assertable 100 cap)).toReal =
      6 * (1 - ρ * (uniformOn (moreThan 120)).real (moreThan cap)) := by
  rw [toReal_bayesFactor_assertable ρ 100 hcap, toReal_bayesFactor_moreThan100,
    Set.inter_eq_left.mpr (moreThan_antitone (by norm_num))]

/-- The implicature *not more than 150* fails in five of the eight successful bands. -/
theorem uniformOn_moreThan120_real_moreThan150 :
    (uniformOn (moreThan 120)).real (moreThan 150) = 5 / 8 := by
  rw [uniformOn_real_apply, ncard_eq (moreThan 120 ∩ moreThan 150) 5, ncard_eq (moreThan 120) 8]
  norm_num

/-- The implicature of *more than 110*, *not more than 120*, fails in every successful band,
so its pragmatic strength is its semantic strength 12 times the probability of a semantic
interpretation. -/
theorem toReal_bayesFactor_assertable_moreThan110 (ρ : I) :
    (bayesFactor (assertability ρ) (assertable 110 120)).toReal = 12 * (1 - ρ) := by
  rw [toReal_bayesFactor_assertable ρ 110 le_rfl, toReal_bayesFactor_moreThan110,
    uniformOn_real_apply, ncard_eq (moreThan 120 ∩ moreThan 110 ∩ moreThan 120) 8,
    ncard_eq (moreThan 120 ∩ moreThan 110) 8]
  ring

theorem relevance_assertable_moreThan100 (ρ : I) :
    relevance (assertability ρ) (assertable 100 150) = Real.log (6 * (1 - 5 / 8 * ρ)) := by
  rw [relevance, toReal_bayesFactor_assertable_moreThan100 ρ (by norm_num),
    uniformOn_moreThan120_real_moreThan150, mul_comm (ρ : ℝ)]

theorem relevance_assertable_moreThan110 (ρ : I) :
    relevance (assertability ρ) (assertable 110 120) = Real.log (12 * (1 - ρ)) :=
  congrArg Real.log (toReal_bayesFactor_assertable_moreThan110 ρ)

private theorem bayesFactor_assertable_ne_top (ρ : I) {n cap : ℕ} (hcap : 120 ≤ cap)
    (h : ((moreThan 120)ᶜ ∩ moreThan n).Nonempty) :
    bayesFactor (assertability ρ) (assertable n cap) ≠ ⊤ := by
  refine bayesFactor_ne_top ((measureReal_ne_zero_iff).mp ?_)
  rw [real_assertable_of_failure ρ n hcap, measureReal_ne_zero_iff]
  exact (uniformOn_eq_zero_iff (Set.toFinite _)).not.mpr h.ne_empty

/-- Pragmatically, *more than 100* remains positive evidence for success at every enrichment
rate. -/
theorem posRelevant_assertable_moreThan100 (ρ : I) :
    posRelevant (assertability ρ) (assertable 100 150) := by
  rw [posRelevant_iff_one_lt_toReal (bayesFactor_assertable_ne_top ρ (by norm_num) ⟨10, by decide⟩),
    toReal_bayesFactor_assertable_moreThan100 ρ (by norm_num),
    uniformOn_moreThan120_real_moreThan150]
  linarith [le_one ρ]

/-- Pragmatically, *more than 110* remains positive evidence for success iff the hearer
enriches less than eleven times in twelve. -/
theorem posRelevant_assertable_moreThan110_iff (ρ : I) :
    posRelevant (assertability ρ) (assertable 110 120) ↔ (ρ : ℝ) < 11 / 12 := by
  rw [posRelevant_iff_one_lt_toReal (bayesFactor_assertable_ne_top ρ le_rfl ⟨11, by decide⟩),
    toReal_bayesFactor_assertable_moreThan110]
  constructor <;> intro <;> linarith

/-! ### The reversal -/

/-- When *more than 100* implicates *not more than cap* for a cap at or above the goal, it is
the stronger pragmatic argument iff the rate times two minus the probability, given success,
that the implicature fails exceeds one. With the vacuous cap 200 a rate above one half
suffices; with cap 120 the order never reverses. -/
theorem bayesFactor_assertable_lt_iff_of_le (ρ : I) {cap : ℕ} (hcap : 120 ≤ cap) :
    bayesFactor (assertability ρ) (assertable 110 120) <
        bayesFactor (assertability ρ) (assertable 100 cap) ↔
      1 < ρ * (2 - (uniformOn (moreThan 120)).real (moreThan cap)) := by
  rw [← ENNReal.toReal_lt_toReal (bayesFactor_assertable_ne_top _ le_rfl ⟨11, by decide⟩)
    (bayesFactor_assertable_ne_top _ hcap ⟨10, by decide⟩),
    toReal_bayesFactor_assertable_moreThan110, toReal_bayesFactor_assertable_moreThan100 ρ hcap]
  constructor <;> intro <;> linarith

/-- For the paper's *not more than 150* the order of the two arguments reverses iff the hearer
enriches more than eight times in eleven. The paper fixes the rate at nine in ten and does not
state the threshold. -/
theorem bayesFactor_assertable_lt_iff (ρ : I) :
    bayesFactor (assertability ρ) (assertable 110 120) <
        bayesFactor (assertability ρ) (assertable 100 150) ↔ 8 / 11 < (ρ : ℝ) := by
  rw [bayesFactor_assertable_lt_iff_of_le ρ (by norm_num), uniformOn_moreThan120_real_moreThan150]
  constructor <;> intro <;> linarith

/-- The paper's illustrative enrichment rate of nine in ten. -/
noncomputable abbrev nineTenths : I := ⟨9 / 10, by norm_num, by norm_num⟩

/-- Semantically *more than 110* is the stronger argument for success, but pragmatically, at
the paper's rate of nine in ten, the order reverses. -/
theorem relevance_reversal :
    relevance success (moreThan 100) < relevance success (moreThan 110) ∧
      relevance (assertability nineTenths) (assertable 110 120) <
        relevance (assertability nineTenths) (assertable 100 150) :=
  ⟨relevance_lt_relevance (bayesFactor_count_ne_zero ⟨12, by decide⟩)
      (bayesFactor_count_ne_top ⟨11, by decide⟩) bayesFactor_moreThan100_lt_moreThan110,
    relevance_lt_relevance
      (ENNReal.toReal_ne_zero.mp (by
        rw [toReal_bayesFactor_assertable_moreThan110]; norm_num [nineTenths])).1
      (bayesFactor_assertable_ne_top _ (by norm_num) ⟨10, by decide⟩)
      ((bayesFactor_assertable_lt_iff _).mpr (by norm_num [nineTenths]))⟩

/-- The paper's pragmatic log (21/8) for *more than 100*. -/
theorem relevance_assertable_moreThan100_nineTenths :
    relevance (assertability nineTenths) (assertable 100 150) = Real.log (21 / 8) := by
  rw [relevance_assertable_moreThan100]
  norm_num [nineTenths]

/-- The paper's pragmatic log (6/5) for *more than 110*. -/
theorem relevance_assertable_moreThan110_nineTenths :
    relevance (assertability nineTenths) (assertable 110 120) = Real.log (6 / 5) := by
  rw [relevance_assertable_moreThan110]
  norm_num [nineTenths]

end CumminsFranke2021

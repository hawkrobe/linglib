import Linglib.Pragmatics.DecisionTheoretic.Basic
import Linglib.Core.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Rational interpretation of numerical quantity

Cummins and Franke measure the argumentative strength of a numerical utterance toward a
speaker's goal by Merin's relevance, the log Bayes factor, once on the utterance's truth
conditions and once on its felicitous assertability, and show that the two can disagree. In
their conference example the goal is that more than 120 people register, registrations are
uniform on [0, 200], and the speaker chooses between *more than 100* and *more than 110*:
semantically the stronger utterance is the stronger argument, but a hearer who reads
*more than 110* as implicating *not more than 120* finds that reading incompatible with the
goal, so under assertability the utterance is only weak evidence and the order reverses.

We derive the semantic ordering from the general fact that shedding worlds where the goal
fails only strengthens an argument, compute the four strengths the paper prints, show that
both utterances remain positive evidence at the paper's enrichment rate, and prove the
reversal with that rate left free: the order reverses exactly when the hearer enriches more
than eight times in eleven. The skeptical-hearer rule of the paper's last theoretical section
and its corpus study are not formalized.

## Implementation notes

* Registrations are binned into twenty bands of width ten under a counting prior; every
  threshold in the example is a band boundary, so the continuous uniform prior is
  represented exactly.
* For *more than 110* the paper prints log 11, which is the Bayes factor of *more than 100*
  toward the goal *more than 110*; toward the stated goal the factor is 12. The ordering is
  unaffected.
* Strengths are natural logarithms; the paper prints base-ten decimals and uses strengths
  only ordinally.

## References

* [C. Cummins and M. Franke, *Rational Interpretation of Numerical Quantity in Argumentative
  Contexts* (2021)][cummins-franke-2021]
* [A. Merin, *Information, Relevance, and Social Decisionmaking: Some Principles and Results
  of Decision-Theoretic Semantics* (1999)][merin-1999-relevance]
-/

namespace CumminsFranke2021

open DTS MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

/-! ### The conference -/

/-- Registration totals in bands of width ten: band `k` covers `(10k, 10(k+1)]`. -/
abbrev Band := Fin 20

/-- The extension of *more than n* for a threshold `n` that is a multiple of ten. -/
def moreThan (n : ℕ) : Set Band := {k | n ≤ 10 * (k : ℕ)}

instance (n : ℕ) : DecidablePred (· ∈ moreThan n) := λ k =>
  inferInstanceAs (Decidable (n ≤ 10 * (k : ℕ)))

theorem moreThan_subset {m n : ℕ} (h : m ≤ n) : moreThan n ⊆ moreThan m := λ _ hk => h.trans hk

/-- The conference succeeds iff more than 120 people register, under the counting prior. -/
noncomputable abbrev success : Context Band := ⟨moreThan 120, .of_discrete, .count⟩

private theorem ncard_eq (s : Set Band) [DecidablePred (· ∈ s)] (n : ℕ)
    (h : s.toFinset.card = n := by decide) : s.ncard = n :=
  (Set.ncard_eq_toFinset_card' s).trans h

/-- Success is at least as probable given *more than 110* as given *more than 100*, since
the bands that *more than 110* sheds are all failures. -/
theorem uniformOn_moreThan100_le_moreThan110 :
    uniformOn (moreThan 100) (moreThan 120) ≤ uniformOn (moreThan 110) (moreThan 120) :=
  cond_le_cond_of_subset _ .of_discrete .of_discrete (moreThan_subset (show 100 ≤ 110 by norm_num))
    (Set.inter_subset_left.trans (moreThan_subset (show 110 ≤ 120 by norm_num)))

/-- Hence *more than 110* is semantically the stronger argument for success. -/
theorem bayesFactor_moreThan100_lt_moreThan110 :
    bayesFactor success (moreThan 100) < bayesFactor success (moreThan 110) :=
  bayesFactor_lt_of_subset success .of_discrete (moreThan_subset (show 100 ≤ 110 by norm_num))
    (Set.inter_subset_left.trans (moreThan_subset (show 110 ≤ 120 by norm_num)))
    (Measure.count_ne_zero_iff.mpr ⟨12, by decide⟩)
    (Measure.count_ne_zero_iff.mpr ⟨10, by decide⟩)

/-- The paper's log 6 for *more than 100*. -/
theorem relevance_moreThan100 : relevance success (moreThan 100) = Real.log 6 := by
  rw [relevance_count, ncard_eq (moreThan 120 ∩ moreThan 100) 8, ncard_eq (moreThan 120) 8,
    ncard_eq ((moreThan 120)ᶜ ∩ moreThan 100) 2, ncard_eq (moreThan 120)ᶜ 12]
  norm_num

/-- *more than 110* toward the stated goal, where the paper prints log 11. -/
theorem relevance_moreThan110 : relevance success (moreThan 110) = Real.log 12 := by
  rw [relevance_count, ncard_eq (moreThan 120 ∩ moreThan 110) 8, ncard_eq (moreThan 120) 8,
    ncard_eq ((moreThan 120)ᶜ ∩ moreThan 110) 1, ncard_eq (moreThan 120)ᶜ 12]
  norm_num

/-- The quantity behind the paper's log 11: *more than 100* toward the goal *more than 110*. -/
theorem relevance_moreThan100_toward110 :
    relevance ⟨moreThan 110, .of_discrete, .count⟩ (moreThan 100) = Real.log 11 := by
  rw [relevance_count, ncard_eq (moreThan 110 ∩ moreThan 100) 9, ncard_eq (moreThan 110) 9,
    ncard_eq ((moreThan 110)ᶜ ∩ moreThan 100) 1, ncard_eq (moreThan 110)ᶜ 11]
  norm_num

/-! ### Assertability

Assertability is stochastic: the hearer enriches the utterance with its scalar implicature
(*more than 100* to *not more than 150*, *more than 110* to *not more than 120*) with
probability `ρ` and reads it literally otherwise, so the utterance is felicitously assertable
iff it is true on the reading drawn. The joint of registrations and readings is the product
of the counting prior with the hearer's coin. -/

/-- How the hearer resolves the utterance. -/
inductive Interpretation where
  | enriched | literal
  deriving DecidableEq

instance : Fintype Interpretation where
  elems := {.enriched, .literal}
  complete := λ x => by cases x <;> simp

instance : MeasurableSpace Interpretation := ⊤

private theorem Interpretation.sum_univ {M : Type*} [AddCommMonoid M] (g : Interpretation → M) :
    ∑ i, g i = g .enriched + g .literal :=
  Finset.sum_pair (by decide)

/-- The hearer enriches with probability `ρ` and reads literally otherwise. -/
noncomputable abbrev hearer (ρ : I) : Measure Interpretation := Ber(.enriched, .literal, ρ)

/-- The readings of *more than n* whose enrichment is *not more than cap*. -/
def reading (n cap : ℕ) : Interpretation → Set Band
  | .enriched => moreThan n \ moreThan cap
  | .literal => moreThan n

/-- The assertability model: registrations paired with the hearer's reading, under the
counting prior and the hearer's coin, with the goal lifted along the registration. -/
noncomputable abbrev assertability (ρ : I) : Context (Band × Interpretation) :=
  ⟨Prod.fst ⁻¹' moreThan 120, measurable_fst .of_discrete, Measure.count.prod (hearer ρ)⟩

/-- *more than n* is felicitously assertable iff it is true on the reading drawn. -/
def assertable (n cap : ℕ) : Set (Band × Interpretation) := {p | p.1 ∈ reading n cap p.2}

/-- Given the registration band, the probability that *more than n* is assertable is the
paper's mixture of its readings' proportions. -/
theorem real_cond_assertable (ρ : I) (S : Set Band) (n cap : ℕ) :
    ((Measure.count.prod (hearer ρ))[|Prod.fst ⁻¹' S]).real (assertable n cap) =
      (uniformOn S).real (moreThan n \ moreThan cap) * ρ +
        (uniformOn S).real (moreThan n) * (1 - ρ) := by
  rw [assertable, Measure.cond_prod_fst_real_fibers _ _ .of_discrete (λ _ => .of_discrete),
    Interpretation.sum_univ]
  simp [reading, uniformOn]

/-- The paper's probability that *more than 100* is assertable given success. -/
theorem real_assertable_moreThan100_of_success (ρ : I) :
    ((assertability ρ).prior[|(assertability ρ).topic]).real (assertable 100 150) =
      3 / 8 * ρ + (1 - ρ) := by
  rw [real_cond_assertable, uniformOn_real_apply, uniformOn_real_apply,
    ncard_eq (moreThan 120 ∩ (moreThan 100 \ moreThan 150)) 3, ncard_eq (moreThan 120) 8,
    ncard_eq (moreThan 120 ∩ moreThan 100) 8]
  ring

/-- The paper's probability that *more than 100* is assertable given failure. -/
theorem real_assertable_moreThan100_of_failure (ρ : I) :
    ((assertability ρ).prior[|(assertability ρ).topicᶜ]).real (assertable 100 150) = 1 / 6 := by
  rw [← Set.preimage_compl, real_cond_assertable, uniformOn_real_apply, uniformOn_real_apply,
    ncard_eq ((moreThan 120)ᶜ ∩ (moreThan 100 \ moreThan 150)) 2, ncard_eq (moreThan 120)ᶜ 12,
    ncard_eq ((moreThan 120)ᶜ ∩ moreThan 100) 2]
  ring

/-- The paper's probability that *more than 110* is assertable given success: only the
literal reading survives, since the enrichment contradicts success. -/
theorem real_assertable_moreThan110_of_success (ρ : I) :
    ((assertability ρ).prior[|(assertability ρ).topic]).real (assertable 110 120) = 1 - ρ := by
  rw [real_cond_assertable, uniformOn_real_apply, uniformOn_real_apply,
    ncard_eq (moreThan 120 ∩ (moreThan 110 \ moreThan 120)) 0, ncard_eq (moreThan 120) 8,
    ncard_eq (moreThan 120 ∩ moreThan 110) 8]
  ring

/-- The paper's probability that *more than 110* is assertable given failure. -/
theorem real_assertable_moreThan110_of_failure (ρ : I) :
    ((assertability ρ).prior[|(assertability ρ).topicᶜ]).real (assertable 110 120) = 1 / 12 := by
  rw [← Set.preimage_compl, real_cond_assertable, uniformOn_real_apply, uniformOn_real_apply,
    ncard_eq ((moreThan 120)ᶜ ∩ (moreThan 110 \ moreThan 120)) 1, ncard_eq (moreThan 120)ᶜ 12,
    ncard_eq ((moreThan 120)ᶜ ∩ moreThan 110) 1]
  ring

/-- Under assertability, *more than 100* loses only the share of successful worlds its
enrichment excludes. -/
theorem toReal_bayesFactor_assertable_moreThan100 (ρ : I) :
    (bayesFactor (assertability ρ) (assertable 100 150)).toReal = 6 * (1 - 5 / 8 * ρ) := by
  rw [bayesFactor_def, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def,
    real_assertable_moreThan100_of_success, real_assertable_moreThan100_of_failure]
  ring

/-- Under assertability, the strength of *more than 110* is scaled by the literal share. -/
theorem toReal_bayesFactor_assertable_moreThan110 (ρ : I) :
    (bayesFactor (assertability ρ) (assertable 110 120)).toReal = 12 * (1 - ρ) := by
  rw [bayesFactor_def, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def,
    real_assertable_moreThan110_of_success, real_assertable_moreThan110_of_failure]
  ring

theorem relevance_assertable_moreThan100 (ρ : I) :
    relevance (assertability ρ) (assertable 100 150) = Real.log (6 * (1 - 5 / 8 * ρ)) :=
  congrArg Real.log (toReal_bayesFactor_assertable_moreThan100 ρ)

theorem relevance_assertable_moreThan110 (ρ : I) :
    relevance (assertability ρ) (assertable 110 120) = Real.log (12 * (1 - ρ)) :=
  congrArg Real.log (toReal_bayesFactor_assertable_moreThan110 ρ)

private theorem assertable_moreThan100_ne_zero (ρ : I) :
    (assertability ρ).prior[|(assertability ρ).topicᶜ] (assertable 100 150) ≠ 0 :=
  (measureReal_ne_zero_iff (measure_ne_top _ _)).mp
    (by rw [real_assertable_moreThan100_of_failure]; norm_num)

private theorem assertable_moreThan110_ne_zero (ρ : I) :
    (assertability ρ).prior[|(assertability ρ).topicᶜ] (assertable 110 120) ≠ 0 :=
  (measureReal_ne_zero_iff (measure_ne_top _ _)).mp
    (by rw [real_assertable_moreThan110_of_failure]; norm_num)

/-- Under assertability *more than 100* remains positive evidence for success at every
enrichment rate. -/
theorem posRelevant_assertable_moreThan100 (ρ : I) :
    posRelevant (assertability ρ) (assertable 100 150) :=
  (posRelevant_iff_one_lt_toReal (bayesFactor_ne_top (assertable_moreThan100_ne_zero ρ))).mpr
    (by rw [toReal_bayesFactor_assertable_moreThan100]; nlinarith [le_one ρ])

/-- Under assertability *more than 110* remains positive evidence for success iff the hearer
enriches less than eleven times in twelve. -/
theorem posRelevant_assertable_moreThan110_iff (ρ : I) :
    posRelevant (assertability ρ) (assertable 110 120) ↔ (ρ : ℝ) < 11 / 12 := by
  rw [posRelevant_iff_one_lt_toReal (bayesFactor_ne_top (assertable_moreThan110_ne_zero ρ)),
    toReal_bayesFactor_assertable_moreThan110]
  constructor <;> intro <;> linarith

/-! ### The reversal -/

/-- The order of the two arguments reverses under assertability iff the hearer enriches more
than eight times in eleven. The paper fixes the rate at nine in ten and does not state the
threshold. -/
theorem bayesFactor_assertable_lt_iff (ρ : I) :
    bayesFactor (assertability ρ) (assertable 110 120) <
        bayesFactor (assertability ρ) (assertable 100 150) ↔ 8 / 11 < (ρ : ℝ) := by
  rw [← ENNReal.toReal_lt_toReal (bayesFactor_ne_top (assertable_moreThan110_ne_zero ρ))
    (bayesFactor_ne_top (assertable_moreThan100_ne_zero ρ)),
    toReal_bayesFactor_assertable_moreThan110, toReal_bayesFactor_assertable_moreThan100]
  constructor <;> intro <;> linarith

/-- The paper's illustrative enrichment rate of nine in ten. -/
noncomputable abbrev nineTenths : I := ⟨9 / 10, by norm_num, by norm_num⟩

/-- The paper's demonstration: semantically *more than 110* is the stronger argument for
success, but under assertability at nine in ten the order reverses. -/
theorem relevance_reversal :
    relevance success (moreThan 100) < relevance success (moreThan 110) ∧
      relevance (assertability nineTenths) (assertable 110 120) <
        relevance (assertability nineTenths) (assertable 100 150) :=
  ⟨relevance_lt_relevance (bayesFactor_count_ne_zero ⟨12, by decide⟩)
      (bayesFactor_count_ne_top ⟨11, by decide⟩) bayesFactor_moreThan100_lt_moreThan110,
    relevance_lt_relevance
      (bayesFactor_ne_zero ((measureReal_ne_zero_iff (measure_ne_top _ _)).mp
        (by rw [real_assertable_moreThan110_of_success]; norm_num [nineTenths])))
      (bayesFactor_ne_top (assertable_moreThan100_ne_zero _))
      ((bayesFactor_assertable_lt_iff _).mpr (by norm_num [nineTenths]))⟩

/-- The paper's log (21/8) for *more than 100* under assertability. -/
theorem relevance_assertable_moreThan100_nineTenths :
    relevance (assertability nineTenths) (assertable 100 150) = Real.log (21 / 8) := by
  rw [relevance_assertable_moreThan100]
  norm_num [nineTenths]

/-- The paper's log (6/5) for *more than 110* under assertability. -/
theorem relevance_assertable_moreThan110_nineTenths :
    relevance (assertability nineTenths) (assertable 110 120) = Real.log (6 / 5) := by
  rw [relevance_assertable_moreThan110]
  norm_num [nineTenths]

end CumminsFranke2021

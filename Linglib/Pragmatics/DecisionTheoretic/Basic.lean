module

public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.LikelihoodRatio
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Questions.Hamblin
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Decision.Risk.Countable
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Decision-Theoretic Semantics

This file sets up the core of Merin's Decision-Theoretic Semantics (DTS) [merin-1999-relevance]:
meaning explicated through the *signed relevance* of a proposition E to one side H of a
dichotomic issue {H, ¬H}, the log Bayes factor log (P(E∣H) / P(E∣¬H)).

A context is a binary statistical model in the sense of mathlib's statistical decision theory
(`Mathlib.Probability.Decision`): each side of the issue generates data from the prior
conditioned on it (`Context.conditional`), the pair packages as a kernel out of `Bool`
(`Context.hypothesisKernel`, the shape of Degenne's `twoHypKernel`), and `bayesFactor` is
`ProbabilityTheory.likelihoodRatio` of the two conditionals. The Bayes-factor algebra lives at
the two-measure level in `Core.Probability.LikelihoodRatio`; this file adds the issue vocabulary
and the facts that concern the joint prior. The paper's applications to *or*, *but*, *even*, and
*also* are in `Studies/Merin1999a.lean`.

## Main definitions

- `Context`: a dichotomic issue (`topic : Set W`, with its measurability witness) plus a prior
  (Partial Definition 6); `Context.Nondegenerate` marks a live issue
- `bayesFactor`: the likelihood ratio of the induced testing problem
- `relevance`: its logarithm, Merin's relevance of E to H (Definition 4)
- `posRelevant`, `negRelevant`, `irrelevant`: the relevance signs (Definition 5)
- `hContrary`: A and B have opposite relevance signs
- `CondIndepIssue`: independence of A and B conditionally on H and on ¬H (Definition 9), the
  content of the Conditional Independence Presumption (Hypothesis 2)

## Main results

- `sign_reversal`: BF_H(E) · BF_¬H(E) = 1 (Corollary 3)
- `relevance_eq_neg_log_sub_neg_log`: relevance is the differential of conditional
  informativeness (Fact 2)
- `CondIndepIssue.bayesFactor_inter`: under issue-conditional independence, BF(A∧B) =
  BF(A) · BF(B) (Fact 5); Theorem 6a's order of conjunction, disjuncts, and disjunction is
  `CondIndepIssue.max_bayesFactor_lt_inter`, `.bayesFactor_union_lt_max`, and
  `.one_lt_bayesFactor_union`
- `posRelevant_of_lt_cond`: evidence that H makes more probable confirms H
- `avgRisk_hypothesisKernel`: the average risk of an estimator against the induced problem, in
  its finite two-point form
- `bayesFactor_lt_of_subset`: shedding ¬H-worlds from an utterance strengthens it as an argument
  for H
- `relevance_count`, `condIndepIssue_count_iff`: over a counting prior, relevance is the log ratio
  of proportions and issue-conditional independence is a product equation of cardinalities

## Implementation notes

The polar question {H, ¬H} is not a separate wrapper type: the context stores H, and the
question is recovered by `Context.toQuestion`. Relevance is carried by `bayesFactor` in `ℝ≥0∞`,
where the boundary cases P(E∣¬H) = 0 and P(E∣H) = 0 take their true values `∞` and `0`
(Merin's r = ±∞); `relevance` is the real logarithm, which sends both to `0`, so sign and
order facts are stated on `bayesFactor`.

## References

* [merin-1999-relevance]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DTS

/-! ### Contexts -/

/-- A DTS context (Partial Definition 6): the proposition H at issue, with ¬H implicit, and a
prior over worlds. -/
structure Context (W : Type*) [MeasurableSpace W] where
  /-- The hypothesis H. -/
  topic : Set W
  /-- Measurability of the topic, so that conditioning on H and ¬H is well-behaved. -/
  topicMeasurable : MeasurableSet topic
  /-- Prior measure over worlds. Conditioning normalizes, so an unnormalized prior (e.g.
  `Measure.count`) induces the same relevance facts as its normalization. -/
  prior : Measure W

variable {W : Type*} [MeasurableSpace W]

/-- Swap the issue: replace H with ¬H. -/
def swapIssue (ctx : Context W) : Context W :=
  { topic := ctx.topicᶜ,
    topicMeasurable := ctx.topicMeasurable.compl,
    prior := ctx.prior }

/-- The issue {H, ¬H} as the polar question of H. -/
def Context.toQuestion (ctx : Context W) : Question W :=
  Question.polar ctx.topic

/-- The issue rules out no worlds; only an answer to it does. -/
@[simp] theorem Context.toQuestion_info (ctx : Context W) : ctx.toQuestion.info = Set.univ :=
  Question.info_polar _

/-- The issue is inquisitive iff H is neither everything nor nothing. -/
theorem Context.toQuestion_isInquisitive_iff (ctx : Context W) :
    ctx.toQuestion.isInquisitive ↔ ctx.topic ≠ ∅ ∧ ctx.topic ≠ Set.univ :=
  Question.isInquisitive_polar_iff _

/-! ### The induced binary testing problem

A context is a binary statistical model: the parameter space is `Bool`,
and each side of the issue generates data from the prior conditioned on
it. `Context.conditional` is the model's family of data-generating
distributions and `Context.hypothesisKernel` packages it as the kernel of
the testing problem (the shape of Degenne's `twoHypKernel μ ν`). -/

/-- The data-generating distribution of each side of the issue: the prior
conditioned on H (at `true`) or on ¬H (at `false`). -/
noncomputable def Context.conditional (ctx : Context W) : Bool → Measure W
  | true => ctx.prior[|ctx.topic]
  | false => ctx.prior[|ctx.topicᶜ]

@[simp] theorem Context.conditional_true (ctx : Context W) :
    ctx.conditional true = ctx.prior[|ctx.topic] := rfl

@[simp] theorem Context.conditional_false (ctx : Context W) :
    ctx.conditional false = ctx.prior[|ctx.topicᶜ] := rfl

/-- Swapping the issue reindexes the conditionals along negation. -/
theorem Context.conditional_swapIssue (ctx : Context W) (θ : Bool) :
    (swapIssue ctx).conditional θ = ctx.conditional (!θ) := by
  cases θ <;> simp [Context.conditional, swapIssue, compl_compl]

/-- The data-generating kernel of the induced binary testing problem. -/
noncomputable def Context.hypothesisKernel (ctx : Context W) : Kernel Bool W :=
  .ofFunOfCountable ctx.conditional

/-- The parameter prior of the induced binary testing problem: the issue
splits the prior's total mass. -/
noncomputable def Context.hypothesisPrior (ctx : Context W) : Measure Bool :=
  ctx.prior ctx.topic • Measure.dirac true + ctx.prior ctx.topicᶜ • Measure.dirac false

@[simp] theorem Context.hypothesisKernel_apply (ctx : Context W) (θ : Bool) :
    ctx.hypothesisKernel θ = ctx.conditional θ := rfl

@[simp] theorem Context.hypothesisPrior_true (ctx : Context W) :
    ctx.hypothesisPrior {true} = ctx.prior ctx.topic := by
  simp [Context.hypothesisPrior, Measure.dirac_apply' _ (MeasurableSet.singleton _)]

@[simp] theorem Context.hypothesisPrior_false (ctx : Context W) :
    ctx.hypothesisPrior {false} = ctx.prior ctx.topicᶜ := by
  simp [Context.hypothesisPrior, Measure.dirac_apply' _ (MeasurableSet.singleton _)]

/-- A live issue: both sides carry mass. Merin's dichotomic issue {H, ¬H}
presupposes a genuine question, so the degenerate cases are excluded at the
level of the object rather than per theorem. -/
class Context.Nondegenerate (ctx : Context W) : Prop where
  topic_ne_zero : ctx.prior ctx.topic ≠ 0
  compl_ne_zero : ctx.prior ctx.topicᶜ ≠ 0

instance (ctx : Context W) [h : ctx.Nondegenerate] : (swapIssue ctx).Nondegenerate :=
  ⟨h.compl_ne_zero, by simpa [swapIssue, compl_compl] using h.topic_ne_zero⟩

/-- Each side's conditional is a genuine probability measure over a live
issue. -/
theorem Context.isProbabilityMeasure_conditional (ctx : Context W)
    [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] (θ : Bool) :
    IsProbabilityMeasure (ctx.conditional θ) := by
  cases θ
  · exact cond_isProbabilityMeasure Context.Nondegenerate.compl_ne_zero
  · exact cond_isProbabilityMeasure Context.Nondegenerate.topic_ne_zero

instance (ctx : Context W) (θ : Bool) :
    IsZeroOrProbabilityMeasure (ctx.conditional θ) := by
  cases θ <;> · rw [Context.conditional]; infer_instance

/-! ### Bayes factor and relevance -/

/-- Bayes factor: P(E∣H) / P(E∣¬H), in `ℝ≥0∞` — the likelihood ratio of the
induced binary testing problem. Total division gives the boundary cases
their true values: P(E∣¬H) = 0 with P(E∣H) > 0 is `∞` (infinitely strong
evidence for H), and 0/0 = 0. -/
noncomputable def bayesFactor (ctx : Context W) (e : Set W) : ℝ≥0∞ :=
  likelihoodRatio (ctx.conditional true) (ctx.conditional false) e

theorem bayesFactor_def (ctx : Context W) (e : Set W) :
    bayesFactor ctx e = ctx.prior[|ctx.topic] e / ctx.prior[|ctx.topicᶜ] e := rfl

/-- `bayesFactor` is the likelihood ratio of the induced testing problem. -/
theorem bayesFactor_eq_hypothesisKernel_div (ctx : Context W) (e : Set W) :
    bayesFactor ctx e = ctx.hypothesisKernel true e / ctx.hypothesisKernel false e := rfl

/-- Merin's relevance of E to H (Definition 4), the log Bayes factor, real-valued through
`ENNReal.toReal`: the boundary cases `0` and `∞` both land at `Real.log 0 = 0`,
so sign and order facts are read off `bayesFactor` itself
(`posRelevant_iff_one_lt_toReal`, `relevance_lt_relevance`). -/
noncomputable def relevance (ctx : Context W) (e : Set W) : ℝ :=
  Real.log (bayesFactor ctx e).toReal

theorem bayesFactor_ne_zero {ctx : Context W} {e : Set W} (h : ctx.prior[|ctx.topic] e ≠ 0) :
    bayesFactor ctx e ≠ 0 := by
  rw [bayesFactor_def]
  exact ENNReal.div_ne_zero.mpr ⟨h, measure_ne_top _ _⟩

theorem bayesFactor_ne_top {ctx : Context W} {e : Set W} (h : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    bayesFactor ctx e ≠ ⊤ := by
  rw [bayesFactor_def]
  exact (ENNReal.div_lt_top (measure_ne_top _ _) h).ne

/-- Relevance is strictly monotone in the Bayes factor away from the boundary cases. -/
theorem relevance_lt_relevance {ctx : Context W} {e₁ e₂ : Set W} (h₁ : bayesFactor ctx e₁ ≠ 0)
    (h₂ : bayesFactor ctx e₂ ≠ ⊤) (h : bayesFactor ctx e₁ < bayesFactor ctx e₂) :
    relevance ctx e₁ < relevance ctx e₂ :=
  Real.log_lt_log (ENNReal.toReal_pos h₁ (ne_top_of_lt h))
    ((ENNReal.toReal_lt_toReal (ne_top_of_lt h) h₂).mpr h)

/-- E is positively relevant to H, BF > 1 (Definition 5): E confirms H. -/
def posRelevant (ctx : Context W) (e : Set W) : Prop :=
  1 < bayesFactor ctx e

theorem posRelevant_iff_one_lt_toReal {ctx : Context W} {e : Set W}
    (ht : bayesFactor ctx e ≠ ⊤) : posRelevant ctx e ↔ 1 < (bayesFactor ctx e).toReal := by
  rw [posRelevant, ← ENNReal.toReal_lt_toReal ENNReal.one_ne_top ht, ENNReal.toReal_one]

/-- E is negatively relevant to H, BF < 1 (Definition 5): E disconfirms H. -/
def negRelevant (ctx : Context W) (e : Set W) : Prop :=
  bayesFactor ctx e < 1

theorem negRelevant_iff_toReal_lt_one {ctx : Context W} {e : Set W}
    (ht : bayesFactor ctx e ≠ ⊤) : negRelevant ctx e ↔ (bayesFactor ctx e).toReal < 1 := by
  rw [negRelevant, ← ENNReal.toReal_lt_toReal ht ENNReal.one_ne_top, ENNReal.toReal_one]

/-- E is irrelevant to H, BF = 1 (Definition 5): E neither confirms nor disconfirms H. -/
def irrelevant (ctx : Context W) (e : Set W) : Prop :=
  bayesFactor ctx e = 1

/-- A and B are H-contrary: they have opposite nonzero relevance signs, one supporting H and
the other ¬H. -/
def hContrary (ctx : Context W) (a b : Set W) : Prop :=
  (posRelevant ctx a ∧ negRelevant ctx b) ∨ (negRelevant ctx a ∧ posRelevant ctx b)

/-- `bayesFactor` under the swapped issue, with the double complement
reduced. -/
theorem bayesFactor_swapIssue (ctx : Context W) (e : Set W) :
    bayesFactor (swapIssue ctx) e =
      ctx.prior[|ctx.topicᶜ] e / ctx.prior[|ctx.topic] e := by
  simp [bayesFactor, likelihoodRatio, swapIssue, compl_compl]

/-! ### Monotonicity

Shedding ¬H-worlds from an utterance can only strengthen it as an argument for
H: the H-side conditional is unchanged and the ¬H-side conditional can only
fall. -/

/-- If `u₂ ⊆ u₁` and every H-world of `u₁` lies in `u₂`, then `u₂` is at least
as relevant to H as `u₁`. -/
theorem bayesFactor_le_of_subset (ctx : Context W) {u₁ u₂ : Set W}
    (hsub : u₂ ⊆ u₁) (hent : ctx.topic ∩ u₁ ⊆ u₂) :
    bayesFactor ctx u₁ ≤ bayesFactor ctx u₂ := by
  have h : ctx.topic ∩ u₁ = ctx.topic ∩ u₂ :=
    Set.Subset.antisymm (fun w hw ↦ ⟨hw.1, hent hw⟩) (Set.inter_subset_inter_right _ hsub)
  rw [bayesFactor_def, bayesFactor_def, cond_apply ctx.topicMeasurable,
    cond_apply ctx.topicMeasurable, h]
  exact ENNReal.div_le_div_left (measure_mono hsub) _

/-- Strictly so once the shed worlds carry mass and `u₂` is possible under H. -/
theorem bayesFactor_lt_of_subset (ctx : Context W) [IsFiniteMeasure ctx.prior]
    {u₁ u₂ : Set W} (hu₂ : MeasurableSet u₂) (hsub : u₂ ⊆ u₁) (hent : ctx.topic ∩ u₁ ⊆ u₂)
    (hpos : ctx.prior (ctx.topic ∩ u₂) ≠ 0) (hgap : ctx.prior (u₁ \ u₂) ≠ 0) :
    bayesFactor ctx u₁ < bayesFactor ctx u₂ := by
  have h : ctx.topic ∩ u₁ = ctx.topic ∩ u₂ :=
    Set.Subset.antisymm (fun w hw ↦ ⟨hw.1, hent hw⟩) (Set.inter_subset_inter_right _ hsub)
  have hgap' : u₁ \ u₂ ⊆ ctx.topicᶜ := fun w hw h ↦ hw.2 (hent ⟨h, hw.1⟩)
  have hd : ctx.prior[|ctx.topicᶜ] u₂ < ctx.prior[|ctx.topicᶜ] u₁ := by
    rw [cond_apply ctx.topicMeasurable.compl, cond_apply ctx.topicMeasurable.compl,
      ← measure_inter_add_sdiff (ctx.topicᶜ ∩ u₁) hu₂, Set.inter_sdiff_assoc,
      Set.inter_eq_right.mpr hgap', Set.inter_assoc, Set.inter_eq_right.mpr hsub]
    exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr (measure_ne_top ctx.prior _))
      (ENNReal.inv_ne_top.mpr fun h0 ↦ hgap (measure_mono_null hgap' h0))
      (ENNReal.lt_add_right (measure_ne_top ctx.prior _) hgap)
  rw [bayesFactor_def, bayesFactor_def, cond_apply ctx.topicMeasurable,
    cond_apply ctx.topicMeasurable, h]
  exact ENNReal.div_lt_div_left
    (mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top ctx.prior _)) hpos)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr fun h ↦ hpos
      (measure_mono_null Set.inter_subset_left h)) (measure_ne_top ctx.prior _)) hd

/-! ### Counting priors

Over a finite type with the counting prior, the Bayes factor is a ratio of
proportions and relevance its logarithm. The real-valued forms need no side
conditions: the junk values agree (`0 / 0 = 0` in `ℝ`, `Real.log 0 = 0`). -/

section Count

variable [Fintype W] [MeasurableSingletonClass W] (topic e : Set W)

theorem toReal_bayesFactor_count :
    (bayesFactor ⟨topic, .of_discrete, .count⟩ e).toReal =
      ((topic ∩ e).ncard / topic.ncard) / ((topicᶜ ∩ e).ncard / topicᶜ.ncard) := by
  rw [bayesFactor_def, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def]
  exact congrArg₂ (· / ·) (uniformOn_real_apply topic e) (uniformOn_real_apply topicᶜ e)

theorem relevance_count :
    relevance ⟨topic, .of_discrete, .count⟩ e =
      Real.log (((topic ∩ e).ncard / topic.ncard) / ((topicᶜ ∩ e).ncard / topicᶜ.ncard)) :=
  congrArg Real.log (toReal_bayesFactor_count topic e)

variable {topic e}

theorem bayesFactor_count_ne_zero (h : (topic ∩ e).Nonempty) :
    bayesFactor ⟨topic, .of_discrete, .count⟩ e ≠ 0 :=
  bayesFactor_ne_zero ((uniformOn_eq_zero_iff (Set.toFinite _)).not.mpr h.ne_empty)

theorem bayesFactor_count_ne_top (h : (topicᶜ ∩ e).Nonempty) :
    bayesFactor ⟨topic, .of_discrete, .count⟩ e ≠ ⊤ :=
  bayesFactor_ne_top ((uniformOn_eq_zero_iff (Set.toFinite _)).not.mpr h.ne_empty)

end Count

/-! ### Cross-product characterizations

The relevance signs in real-valued cross-product mass form — the ENNReal→ℝ
transfer done once, edge cases included; the particle files consume these. -/

/-- Positive relevance as a cross-product of real masses: E confirms H iff
the H-side mass of E outweighs its ¬H-side mass after weighting each by the
opposite cell of the issue. -/
theorem posRelevant_iff_real_cross (ctx : Context W) [IsFiniteMeasure ctx.prior]
    [ctx.Nondegenerate] {e : Set W} :
    posRelevant ctx e ↔
      (ctx.prior (ctx.topicᶜ ∩ e)).toReal * (ctx.prior ctx.topic).toReal <
      (ctx.prior (ctx.topic ∩ e)).toReal * (ctx.prior ctx.topicᶜ).toReal := by
  have hH := Context.Nondegenerate.topic_ne_zero (ctx := ctx)
  have hNH := Context.Nondegenerate.compl_ne_zero (ctx := ctx)
  have hHm := ctx.topicMeasurable
  have hpH : 0 < (ctx.prior ctx.topic).toReal :=
    ENNReal.toReal_pos hH (measure_ne_top _ _)
  have hpNH : 0 < (ctx.prior ctx.topicᶜ).toReal :=
    ENNReal.toReal_pos hNH (measure_ne_top _ _)
  simp only [posRelevant, bayesFactor, likelihoodRatio, Context.conditional_true,
    Context.conditional_false]
  rcases eq_or_ne (ctx.prior[|ctx.topicᶜ] e) 0 with hz | hz
  · have hzm : ctx.prior (ctx.topicᶜ ∩ e) = 0 :=
      (mul_eq_zero.mp ((cond_apply hHm.compl ctx.prior e).symm.trans hz)).resolve_left
        (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    have hiff : 1 < ctx.prior[|ctx.topic] e / ctx.prior[|ctx.topicᶜ] e ↔
        ctx.prior (ctx.topic ∩ e) ≠ 0 := by
      rw [hz]
      constructor
      · intro hpos h0
        rw [cond_apply hHm ctx.prior e, h0, mul_zero, ENNReal.zero_div] at hpos
        exact absurd hpos (by simp)
      · intro hne
        rw [ENNReal.div_zero (by
          rw [cond_apply hHm ctx.prior e]
          exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hne)]
        exact ENNReal.one_lt_top
    rw [hiff, hzm]
    simp only [ENNReal.toReal_zero, zero_mul]
    constructor
    · intro hne
      exact mul_pos (ENNReal.toReal_pos hne (measure_ne_top _ _)) hpNH
    · intro hcross h0
      rw [h0] at hcross
      simp at hcross
  · rw [ENNReal.lt_div_iff_mul_lt (Or.inl hz)
      (Or.inl (cond_apply_ne_top _ hHm.compl e)), one_mul,
      ← ENNReal.toReal_lt_toReal (cond_apply_ne_top _ hHm.compl e)
        (cond_apply_ne_top _ hHm e),
      cond_real_apply _ hHm.compl e, cond_real_apply _ hHm e,
      div_lt_div_iff₀ hpNH hpH]

/-- Negative relevance as a cross-product of real masses, for a live
proposition E (one of nonzero mass; a null E is vacuously negatively
relevant but has a degenerate cross-product). -/
theorem negRelevant_iff_real_cross (ctx : Context W) [IsFiniteMeasure ctx.prior]
    [ctx.Nondegenerate] {e : Set W} (he : ctx.prior e ≠ 0) :
    negRelevant ctx e ↔
      (ctx.prior (ctx.topic ∩ e)).toReal * (ctx.prior ctx.topicᶜ).toReal <
      (ctx.prior (ctx.topicᶜ ∩ e)).toReal * (ctx.prior ctx.topic).toReal := by
  have hH := Context.Nondegenerate.topic_ne_zero (ctx := ctx)
  have hNH := Context.Nondegenerate.compl_ne_zero (ctx := ctx)
  have hHm := ctx.topicMeasurable
  have hpH : 0 < (ctx.prior ctx.topic).toReal :=
    ENNReal.toReal_pos hH (measure_ne_top _ _)
  have hpNH : 0 < (ctx.prior ctx.topicᶜ).toReal :=
    ENNReal.toReal_pos hNH (measure_ne_top _ _)
  simp only [negRelevant, bayesFactor, likelihoodRatio, Context.conditional_true,
    Context.conditional_false]
  rcases eq_or_ne (ctx.prior[|ctx.topicᶜ] e) 0 with hz | hz
  · have hzm : ctx.prior (ctx.topicᶜ ∩ e) = 0 :=
      (mul_eq_zero.mp ((cond_apply hHm.compl ctx.prior e).symm.trans hz)).resolve_left
        (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    refine iff_of_false (fun hneg ↦ ?_) ?_
    · rcases eq_or_ne (ctx.prior[|ctx.topic] e) 0 with h0 | h0
      · have hzH : ctx.prior (ctx.topic ∩ e) = 0 :=
          (mul_eq_zero.mp ((cond_apply hHm ctx.prior e).symm.trans h0)).resolve_left
            (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
        have htot := real_total ctx.prior hHm e
        rw [hzH, hzm] at htot
        simp only [ENNReal.toReal_zero, add_zero] at htot
        exact he (((ENNReal.toReal_eq_zero_iff _).mp htot.symm).resolve_right
          (measure_ne_top _ _))
      · rw [hz, ENNReal.div_zero h0] at hneg
        exact absurd hneg (by simp)
    · rw [hzm]
      simp only [ENNReal.toReal_zero, zero_mul, not_lt]
      positivity
  · rw [ENNReal.div_lt_iff (Or.inl hz)
      (Or.inl (cond_apply_ne_top _ hHm.compl e)), one_mul,
      ← ENNReal.toReal_lt_toReal (cond_apply_ne_top _ hHm e)
        (cond_apply_ne_top _ hHm.compl e),
      cond_real_apply _ hHm.compl e, cond_real_apply _ hHm e,
      div_lt_div_iff₀ hpH hpNH]

/-! ### Issue-conditional independence -/

/-- A and B are independent conditionally on H and on ¬H (Definition 9): mathlib's `IndepSet` at
both conditionals. Merin's Conditional Independence Presumption (Hypothesis 2) is that
interpretation assumes this of coordinated sisters unless something suggests otherwise. -/
def CondIndepIssue (ctx : Context W) (a b : Set W) : Prop :=
  ∀ θ, IndepSet a b (ctx.conditional θ)

/-- The product-equation characterization of issue-conditional
independence: P(A∧B∣H) = P(A∣H)·P(B∣H) and likewise given ¬H. -/
theorem condIndepIssue_iff (ctx : Context W) {a b : Set W}
    (ham : MeasurableSet a) (hbm : MeasurableSet b) :
    CondIndepIssue ctx a b ↔
      (ctx.prior[|ctx.topic] (a ∩ b) =
        ctx.prior[|ctx.topic] a * ctx.prior[|ctx.topic] b ∧
      ctx.prior[|ctx.topicᶜ] (a ∩ b) =
        ctx.prior[|ctx.topicᶜ] a * ctx.prior[|ctx.topicᶜ] b) := by
  refine ⟨fun h ↦ ⟨(h true).measure_inter_eq_mul, (h false).measure_inter_eq_mul⟩,
    fun h θ ↦ ?_⟩
  cases θ
  · exact (indepSet_iff_measure_inter_eq_mul ham hbm _).mpr h.2
  · exact (indepSet_iff_measure_inter_eq_mul ham hbm _).mpr h.1

section Count

variable [Fintype W] [MeasurableSingletonClass W] {topic a b : Set W}

private theorem indepSet_uniformOn_iff (s : Set W) :
    IndepSet a b (uniformOn s) ↔
      (s ∩ (a ∩ b)).ncard * s.ncard = (s ∩ a).ncard * (s ∩ b).ncard := by
  rw [indepSet_iff_measure_inter_eq_mul .of_discrete .of_discrete (uniformOn s),
    ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    uniformOn_real_apply, uniformOn_real_apply, uniformOn_real_apply]
  rcases Nat.eq_zero_or_pos s.ncard with h0 | h0
  · have hz : ∀ t, (s ∩ t).ncard = 0 := fun t ↦
      Nat.eq_zero_of_le_zero (h0 ▸ Set.ncard_le_ncard Set.inter_subset_left s.toFinite)
    simp [h0, hz]
  · rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    norm_cast
    rw [← mul_assoc]
    exact ⟨fun h ↦ Nat.eq_of_mul_eq_mul_right h0 h, fun h ↦ by rw [h]⟩

/-- Over a counting prior, issue-conditional independence is the product equation of
cardinalities on each side of the issue. -/
theorem condIndepIssue_count_iff :
    CondIndepIssue ⟨topic, .of_discrete, .count⟩ a b ↔
      (topic ∩ (a ∩ b)).ncard * topic.ncard = (topic ∩ a).ncard * (topic ∩ b).ncard ∧
      (topicᶜ ∩ (a ∩ b)).ncard * topicᶜ.ncard = (topicᶜ ∩ a).ncard * (topicᶜ ∩ b).ncard := by
  rw [CondIndepIssue, Bool.forall_bool, and_comm]
  exact and_congr (indepSet_uniformOn_iff _) (indepSet_uniformOn_iff _)

end Count

/-! ### Sign reversal -/

/-- **Corollary 3** (qualitative sign reversal): E is positively relevant to
H iff E is negatively relevant to ¬H.

The ordinal content of r_H(E) = −r_{¬H}(E). -/
theorem sign_reversal_qual (ctx : Context W) [IsFiniteMeasure ctx.prior]
    (e : Set W)
    (hEH : ctx.prior[|ctx.topic] e ≠ 0)
    (hENotH : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    posRelevant ctx e ↔ negRelevant (swapIssue ctx) e := by
  unfold posRelevant negRelevant
  rw [bayesFactor_swapIssue, bayesFactor_def,
    ENNReal.lt_div_iff_mul_lt (Or.inl hENotH)
      (Or.inl (cond_apply_ne_top _ ctx.topicMeasurable.compl e)), one_mul,
    ENNReal.div_lt_iff (Or.inl hEH)
      (Or.inl (cond_apply_ne_top _ ctx.topicMeasurable e)), one_mul]

/-- **Corollary 3** (quantitative): BF_H(E) · BF_{¬H}(E) = 1.

Exact when both conditional probabilities are nonzero. -/
theorem sign_reversal (ctx : Context W) [IsFiniteMeasure ctx.prior]
    (e : Set W)
    (hEH : ctx.prior[|ctx.topic] e ≠ 0)
    (hENotH : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    bayesFactor ctx e * bayesFactor (swapIssue ctx) e = 1 := by
  rw [bayesFactor_swapIssue]
  exact likelihoodRatio_mul_swap hEH (cond_apply_ne_top _ ctx.topicMeasurable e)
    hENotH (cond_apply_ne_top _ ctx.topicMeasurable.compl e)

/-- **Fact 2**: relevance is the differential of conditional
informativeness — log BF_H(E) = inf(E, ¬H) − inf(E, H), where
inf(E, X) = −log P(E∣X) is the conditional surprisal of E. -/
theorem relevance_eq_neg_log_sub_neg_log (ctx : Context W) (e : Set W)
    (hEH : ctx.prior[|ctx.topic] e ≠ 0)
    (hENotH : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    relevance ctx e =
      (-Real.log (ctx.prior[|ctx.topicᶜ] e).toReal) -
      (-Real.log (ctx.prior[|ctx.topic] e).toReal) :=
  log_likelihoodRatio hEH (measure_ne_top _ _) hENotH (measure_ne_top _ _)

/-! ### Consequences of issue-conditional independence -/

/-- **Fact 5**: Under issue-conditional independence, the Bayes factor is
multiplicative over conjunction: BF(A∧B) = BF(A) · BF(B). -/
theorem CondIndepIssue.bayesFactor_inter {ctx : Context W}
    [IsFiniteMeasure ctx.prior] {a b : Set W}
    (h : CondIndepIssue ctx a b)
    (hNotH' : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    bayesFactor ctx (a ∩ b) = bayesFactor ctx a * bayesFactor ctx b :=
  likelihoodRatio_inter (h true) (h false) hNotH'
    (cond_apply_ne_top _ ctx.topicMeasurable.compl b)

/-- **Theorem 6a** (conjunction): under issue-conditional independence with
both A, B positively relevant, conjunction dominates both conjuncts. -/
theorem CondIndepIssue.max_bayesFactor_lt_inter {ctx : Context W}
    [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] {a b : Set W}
    (h : CondIndepIssue ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNa : ctx.prior[|ctx.topicᶜ] a ≠ 0) (hNb : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    max (bayesFactor ctx a) (bayesFactor ctx b) < bayesFactor ctx (a ∩ b) := by
  have := ctx.isProbabilityMeasure_conditional true
  have := ctx.isProbabilityMeasure_conditional false
  exact max_likelihoodRatio_lt_inter (h true) (h false) hPosA hPosB hNa hNb

/-- **Theorem 6a** (disjunction, upper): under issue-conditional
independence with both A, B positively relevant, the disjunction is
dominated by the stronger disjunct. -/
theorem CondIndepIssue.bayesFactor_union_lt_max {ctx : Context W}
    [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] {a b : Set W}
    (hbm : MeasurableSet b) (h : CondIndepIssue ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNa : ctx.prior[|ctx.topicᶜ] a ≠ 0) (hNb : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    bayesFactor ctx (a ∪ b) < max (bayesFactor ctx a) (bayesFactor ctx b) := by
  have := ctx.isProbabilityMeasure_conditional true
  have := ctx.isProbabilityMeasure_conditional false
  exact likelihoodRatio_union_lt_max hbm (h true) (h false) hPosA hPosB hNa hNb

/-- **Theorem 6a** (disjunction, lower): under issue-conditional
independence with both A, B positively relevant, the disjunction is still
positively relevant. -/
theorem CondIndepIssue.one_lt_bayesFactor_union {ctx : Context W}
    [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] {a b : Set W}
    (hbm : MeasurableSet b) (h : CondIndepIssue ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNa : ctx.prior[|ctx.topicᶜ] a ≠ 0) (hNb : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    1 < bayesFactor ctx (a ∪ b) := by
  have := ctx.isProbabilityMeasure_conditional true
  have := ctx.isProbabilityMeasure_conditional false
  exact one_lt_likelihoodRatio_union hbm (h true) (h false) hPosA hPosB hNa hNb

/-! ### The Bayesian bridge -/

/-- Over a live issue, E confirms H iff H makes E more probable than it is a priori: the
Bayes-theorem bridge between P(E∣H) > P(E) and BF_H(E) > 1. -/
theorem posRelevant_iff_lt_cond (ctx : Context W) [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] (e : Set W) :
    posRelevant ctx e ↔ ctx.prior e < ctx.prior[|ctx.topic] e := by
  have hm := ctx.topicMeasurable
  have hpH : 0 < (ctx.prior ctx.topic).toReal :=
    ENNReal.toReal_pos Context.Nondegenerate.topic_ne_zero (measure_ne_top _ _)
  have hsum : (ctx.prior ctx.topic).toReal + (ctx.prior ctx.topicᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hm, measure_univ, ENNReal.toReal_one]
  rw [posRelevant_iff_real_cross, ← ENNReal.toReal_lt_toReal (measure_ne_top _ _)
    (cond_apply_ne_top _ hm e), cond_real_apply _ hm, ← real_total ctx.prior hm e,
    lt_div_iff₀ hpH, eq_sub_of_add_eq' hsum]
  constructor <;> intro h <;> linarith

/-! ### Risk of the induced problem -/

/-- The average risk of an estimator against the induced testing problem,
in its finite two-point form: the loss on each side of the issue weighted
by that side's prior mass (the countable-space register of
`Mathlib.Probability.Decision.Risk.Countable`). -/
theorem avgRisk_hypothesisKernel {𝓨 : Type*} [MeasurableSpace 𝓨] (ctx : Context W)
    (ℓ : Bool → 𝓨 → ℝ≥0∞) (κ : Kernel W 𝓨) :
    avgRisk ℓ ctx.hypothesisKernel κ ctx.hypothesisPrior =
      (∫⁻ y, ℓ true y ∂((κ ∘ₖ ctx.hypothesisKernel) true)) * ctx.prior ctx.topic +
      (∫⁻ y, ℓ false y ∂((κ ∘ₖ ctx.hypothesisKernel) false)) * ctx.prior ctx.topicᶜ := by
  rw [avgRisk_fintype]
  simp

end DTS

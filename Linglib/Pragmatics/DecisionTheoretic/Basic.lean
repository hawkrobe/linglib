import Linglib.Core.Probability.ConditionalProbability
import Linglib.Core.Probability.LikelihoodRatio
import Linglib.Semantics.Questions.Hamblin
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Decision.Risk.Countable
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Decision-Theoretic Semantics: Core
[merin-1999-relevance]

Core definitions for Merin's Decision-Theoretic Semantics (DTS). Meaning is
explicated through *signed relevance* — the Bayes factor P(E∣H)/P(E∣¬H) —
relative to a dichotomic issue {H, ¬H}.

A context is a binary statistical model in the sense of mathlib's
statistical decision theory (`Mathlib.Probability.Decision`): each side of
the issue generates data from the prior conditioned on it
(`Context.conditional`), the pair packages as a kernel out of `Bool`
(`Context.hypothesisKernel`, the shape of Degenne's `twoHypKernel`), and
`bayesFactor` is `ProbabilityTheory.likelihoodRatio` of the two
conditionals. The substance of the Bayes-factor algebra lives at the
two-measure level in `Core.Probability.LikelihoodRatio`; this file adds the
issue vocabulary and the facts that genuinely concern the joint prior.

## Key Definitions

- `Context` — a dichotomic issue (`topic : Set W`, with its measurability
  witness) plus a prior measure; `Context.Nondegenerate` marks a live issue
- `bayesFactor` — the likelihood ratio of the induced testing problem
- `posRelevant` / `negRelevant` / `irrelevant` — ordinal relevance predicates
- `hContrary` — A and B have opposite relevance signs
- `CondIndepIssue` — Merin's Conditional Independence Presumption, as
  mathlib `IndepSet` under both conditionals

## Main Results

- **Corollary 3** (`sign_reversal`): BF_H(E) · BF_{¬H}(E) = 1
- **Fact 2** (`log_bayesFactor`): relevance is the differential of
  conditional informativeness
- **Fact 5** (`CondIndepIssue.bayesFactor_inter`): under issue-conditional
  independence, BF(A∧B) = BF(A) · BF(B); **Theorem 6a** splits into
  `CondIndepIssue.max_bayesFactor_lt_inter`, `.bayesFactor_union_lt_max`,
  and `.one_lt_bayesFactor_union`
- **Theorem 6b** (`xor_not_necessarily_positive`): XOR of two positively
  relevant propositions can be negatively relevant
- `avgRisk_hypothesisKernel`: the average risk of an estimator against the
  induced problem, in its finite two-point form
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal symmDiff

namespace DTS

/-- 4-world example type. Used by `xor_not_necessarily_positive` and
consumers in this directory. -/
inductive World4 where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited

instance : Fintype World4 where
  elems := {.w0, .w1, .w2, .w3}
  complete := fun x => by cases x <;> simp

instance : MeasurableSpace World4 := ⊤
instance : DiscreteMeasurableSpace World4 := ⟨fun _ => trivial⟩

/-! ### Core types -/

/-- A DTS context: a dichotomic hypothesis `topic` (the proposition H, with
¬H implicit) plus a prior measure over worlds.

Following mathlib's `Filter.principal` pattern, the polar interrogative
{H, ¬H} is not packaged as a separate wrapper type — the topic is stored
directly, and the inquisitive view is recovered on demand via
`Context.toCoreIssue`. -/
structure Context (W : Type*) [MeasurableSpace W] where
  /-- The hypothesis H. The dichotomic issue {H, ¬H} is recovered as
      `Question.polar topic`. -/
  topic : Set W
  /-- Measurability of the topic, so that conditioning on H and ¬H is
      well-behaved. Free (`.of_discrete`) on the discrete study enums. -/
  topicMeasurable : MeasurableSet topic
  /-- Prior measure over worlds. Conditioning normalizes, so an
      unnormalized prior (e.g. `Measure.count`) induces the same relevance
      facts as its normalization. -/
  prior : Measure W

variable {W : Type*} [MeasurableSpace W]

/-- Swap the issue: replace H with ¬H. -/
def swapIssue (ctx : Context W) : Context W :=
  { topic := ctx.topicᶜ,
    topicMeasurable := ctx.topicMeasurable.compl,
    prior := ctx.prior }

/-- Forgetful projection from a DTS context to the general `Question`
lattice via the polar interrogative content of the topic proposition. The
two representations agree on the underlying question semantics: a DTS
dichotomy {H, ¬H} is exactly the polar interrogative of H, with two
alternatives ⟦H⟧ and ⟦¬H⟧. -/
def Context.toCoreIssue (ctx : Context W) : Question W :=
  Question.polar {w | ctx.topic w}

/-- Every DTS dichotomic issue is non-informative (`info = univ`): the
question `{H, ¬H}` itself rules out no worlds; only an answer to it does.
Inherited from `Question.info_polar`. -/
@[simp] theorem Context.toCoreIssue_info (ctx : Context W) :
    ctx.toCoreIssue.info = Set.univ :=
  Question.info_polar _

/-- A DTS dichotomy is genuinely inquisitive (raises an unsettled question
over the universal info state) iff its topic is non-trivial: neither
everything nor nothing satisfies H. Inherited from
`Question.isInquisitive_polar_iff`. -/
theorem Context.toCoreIssue_isInquisitive_iff (ctx : Context W) :
    ctx.toCoreIssue.isInquisitive ↔
      {w | ctx.topic w} ≠ ∅ ∧ {w | ctx.topic w} ≠ Set.univ :=
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

/-- E is positively relevant to H: BF > 1 (E confirms H). -/
def posRelevant (ctx : Context W) (e : Set W) : Prop :=
  1 < bayesFactor ctx e

/-- E is negatively relevant to H: BF < 1 (E disconfirms H). -/
def negRelevant (ctx : Context W) (e : Set W) : Prop :=
  bayesFactor ctx e < 1

/-- E is irrelevant to H: BF = 1 (E neither confirms nor disconfirms). -/
def irrelevant (ctx : Context W) (e : Set W) : Prop :=
  bayesFactor ctx e = 1

/-- A and B have opposite relevance signs w.r.t. H.

Merin's "contrariness": one supports H while the other supports ¬H. -/
def hContrary (ctx : Context W) (a b : Set W) : Prop :=
  (posRelevant ctx a ∧ negRelevant ctx b) ∨ (negRelevant ctx a ∧ posRelevant ctx b)

/-- `bayesFactor` under the swapped issue, with the double complement
reduced. -/
theorem bayesFactor_swapIssue (ctx : Context W) (e : Set W) :
    bayesFactor (swapIssue ctx) e =
      ctx.prior[|ctx.topicᶜ] e / ctx.prior[|ctx.topic] e := by
  simp [bayesFactor, likelihoodRatio, swapIssue, compl_compl]

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
    refine iff_of_false (fun hneg => ?_) ?_
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

/-- Merin's Conditional Independence Presumption (Def. 6): A and B are
independent under the prior conditioned on each side of the issue —
mathlib's `IndepSet` at both conditionals. -/
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
  refine ⟨fun h => ⟨(h true).measure_inter_eq_mul, (h false).measure_inter_eq_mul⟩,
    fun h θ => ?_⟩
  cases θ
  · exact (indepSet_iff_measure_inter_eq_mul ham hbm _).mpr h.2
  · exact (indepSet_iff_measure_inter_eq_mul ham hbm _).mpr h.1

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
theorem log_bayesFactor (ctx : Context W) [IsFiniteMeasure ctx.prior]
    (e : Set W)
    (hEH : ctx.prior[|ctx.topic] e ≠ 0)
    (hENotH : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    Real.log (bayesFactor ctx e).toReal =
      (-Real.log (ctx.prior[|ctx.topicᶜ] e).toReal) -
      (-Real.log (ctx.prior[|ctx.topic] e).toReal) :=
  log_likelihoodRatio hEH (cond_apply_ne_top _ ctx.topicMeasurable e)
    hENotH (cond_apply_ne_top _ ctx.topicMeasurable.compl e)

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

/-- Probabilistic support implies positive relevance over a live issue: the
Bayes-theorem bridge P(E∣H) > P(E) ⟹ BF_H(E) > 1. The edge case
P(E ∩ ¬H) = 0 needs no special treatment: the factor is then genuinely
infinite.

Promoted from the IKW2025 Part II "Bayesian-to-DTS bridge" in 0.230.502 —
pure DTS-internal content (no IKW dependency), belongs in DTS Core. -/
theorem posRelevant_of_lt_cond (ctx : Context W) [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] (e : Set W)
    (hSupp : ctx.prior e < ctx.prior[|ctx.topic] e) :
    posRelevant ctx e := by
  set μ := ctx.prior
  set topic := ctx.topic
  have htopic : MeasurableSet topic := ctx.topicMeasurable
  have hH_pos : μ topic ≠ 0 := Context.Nondegenerate.topic_ne_zero
  have hNH_pos : μ topicᶜ ≠ 0 := Context.Nondegenerate.compl_ne_zero
  have hpart : μ (e ∩ topic) + μ (e ∩ topicᶜ) = μ e := by
    simpa [Set.sdiff_eq] using measure_inter_add_sdiff e htopic
  have hEH : μ[|topic] e = (μ topic)⁻¹ * μ (topic ∩ e) :=
    cond_apply htopic μ e
  show 1 < ctx.prior[|ctx.topic] e / ctx.prior[|ctx.topicᶜ] e
  rcases eq_or_ne (μ[|topicᶜ] e) 0 with hz | hz
  · -- P(E∣¬H) = 0: the factor is ∞ once P(E∣H) > 0.
    have hnum : μ[|topic] e ≠ 0 := by
      intro h0
      rw [h0] at hSupp
      exact absurd hSupp (by simp)
    rw [show ctx.prior[|ctx.topicᶜ] e = 0 from hz, ENNReal.div_zero hnum]
    exact ENNReal.one_lt_top
  · -- Main case: cross-multiply in ℝ.
    have hENH : μ[|topicᶜ] e = (μ topicᶜ)⁻¹ * μ (topicᶜ ∩ e) :=
      cond_apply htopic.compl μ e
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hz)
      (Or.inl (cond_apply_ne_top μ htopic.compl e)), one_mul]
    have hHfin := measure_ne_top μ topic
    have hNHfin := measure_ne_top μ topicᶜ
    have hsum1 : μ topic + μ topicᶜ = 1 := prob_add_prob_compl htopic
    set pH := (μ topic).toReal with hpH
    set pNH := (μ topicᶜ).toReal with hpNH
    set pEH := (μ (topic ∩ e)).toReal with hpEH
    set pENH := (μ (topicᶜ ∩ e)).toReal with hpENH
    have hpH_pos : 0 < pH := ENNReal.toReal_pos hH_pos hHfin
    have hpNH_pos : 0 < pNH := ENNReal.toReal_pos hNH_pos hNHfin
    have hpEH_nonneg : 0 ≤ pEH := ENNReal.toReal_nonneg
    have hpENH_nonneg : 0 ≤ pENH := ENNReal.toReal_nonneg
    have hsum1' : pH + pNH = 1 := by
      rw [hpH, hpNH, ← ENNReal.toReal_add hHfin hNHfin, hsum1, ENNReal.toReal_one]
    have hpartR : pEH + pENH = (μ e).toReal := by
      rw [hpEH, hpENH, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      congr 1
      simpa [Set.inter_comm] using hpart
    have hSuppR : (μ e).toReal < pEH / pH := by
      have := ENNReal.toReal_lt_toReal (measure_ne_top μ e)
        (cond_apply_ne_top μ htopic e) |>.mpr hSupp
      rwa [hEH, ENNReal.toReal_mul, ENNReal.toReal_inv, inv_mul_eq_div] at this
    refine ENNReal.toReal_lt_toReal
      (cond_apply_ne_top μ htopic.compl e)
      (cond_apply_ne_top μ htopic e) |>.mp ?_
    rw [hEH, hENH, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_inv, inv_mul_eq_div, inv_mul_eq_div, div_lt_div_iff₀ hpNH_pos hpH_pos]
    nlinarith [hSuppR, hsum1', hpartR, mul_pos hpH_pos hpNH_pos,
      (lt_div_iff₀ hpH_pos).mp hSuppR]

/-- Negative relevance implies non-support: the contrapositive of
`posRelevant_of_lt_cond`. Promoted from IKW2025 Part II in 0.230.502. -/
theorem not_lt_cond_of_negRelevant (ctx : Context W) [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] (e : Set W)
    (hNeg : negRelevant ctx e) :
    ¬ ctx.prior e < ctx.prior[|ctx.topic] e := fun hSupp =>
  absurd (posRelevant_of_lt_cond ctx e hSupp) (lt_asymm hNeg)

/-! ### Exclusive disjunction -/

/-- **Theorem 6b**: XOR of two positively relevant propositions is not
necessarily positively relevant.

Counterexample on `World4`: H = {w0}, A = {w0, w1}, B = {w0, w2}, counting
prior. BF(A) = BF(B) = 3, but A ∆ B = {w1, w2} misses H entirely, so its
Bayes factor is 0. -/
theorem xor_not_necessarily_positive :
    ∃ (ctx : Context World4) (a b : Set World4),
      posRelevant ctx a ∧ posRelevant ctx b ∧ ¬ posRelevant ctx (a ∆ b) := by
  refine ⟨⟨(↑({World4.w0} : Finset World4) : Set World4), .of_discrete, .count⟩,
    ↑({World4.w0, World4.w1} : Finset World4), ↑({World4.w0, World4.w2} : Finset World4),
    ?_, ?_, ?_⟩ <;>
    simp only [posRelevant, bayesFactor, likelihoodRatio, Context.conditional_true,
      Context.conditional_false, cond_apply MeasurableSet.of_discrete,
      ← Finset.coe_compl, ← Finset.coe_inter, ← Finset.coe_symmDiff,
      Measure.count_apply_finset]
  · rw [show ({World4.w0} : Finset World4).card = 1 by decide,
      show ({World4.w0} ∩ {World4.w0, World4.w1} : Finset World4).card = 1 by decide,
      show ({World4.w0}ᶜ : Finset World4).card = 3 by decide,
      show ({World4.w0}ᶜ ∩ {World4.w0, World4.w1} : Finset World4).card = 1 by decide]
    simp only [Nat.cast_one, Nat.cast_ofNat, inv_one]
    norm_num
  · rw [show ({World4.w0} : Finset World4).card = 1 by decide,
      show ({World4.w0} ∩ {World4.w0, World4.w2} : Finset World4).card = 1 by decide,
      show ({World4.w0}ᶜ : Finset World4).card = 3 by decide,
      show ({World4.w0}ᶜ ∩ {World4.w0, World4.w2} : Finset World4).card = 1 by decide]
    simp only [Nat.cast_one, Nat.cast_ofNat, inv_one]
    norm_num
  · rw [show ({World4.w0} ∩ ({World4.w0, World4.w1} ∆ {World4.w0, World4.w2}) :
        Finset World4).card = 0 by decide]
    simp

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

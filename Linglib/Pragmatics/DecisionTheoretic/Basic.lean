import Linglib.Core.Probability.ConditionalProbability
import Linglib.Semantics.Questions.Hamblin
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Kernel.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Decision-Theoretic Semantics: Core
[merin-1999-relevance]

Core definitions for Merin's Decision-Theoretic Semantics (DTS). Meaning is
explicated through *signed relevance* — the Bayes factor P(E∣H)/P(E∣¬H) —
relative to a dichotomic issue {H, ¬H}.

The probability substrate is mathlib's: a context carries a
`MeasureTheory.Measure`, conditioning is `ProbabilityTheory.cond` (`μ[|s]`),
and the Bayes factor lives in `ℝ≥0∞`, where total division gives the edge
cases their true values — P(E∣¬H) = 0 < P(E∣H) is *infinitely* strong
evidence, and 0/0 is the vacuous 0.

## Key Definitions

- `Context` — a dichotomic issue (`topic : Set W`, with its measurability
  witness) plus a prior measure. Following mathlib's `Filter.principal`
  pattern, the polar interrogative is not given a separate wrapper type: the
  `topic` is stored directly, and the inquisitive view is recovered as
  `Context.toCoreIssue ctx = Question.polar {w | ctx.topic w}` at
  consumption sites that need the general inquisitive-content lattice.
- `bayesFactor` — P(E∣H) / P(E∣¬H) in `ℝ≥0∞`
- `posRelevant` / `negRelevant` / `irrelevant` — ordinal relevance predicates
- `hContrary` — A and B have opposite relevance signs
- `CIP` — Conditional Independence Presumption

## Main Results

- **Corollary 3** (`sign_reversal`): BF_H(E) · BF_{¬H}(E) = 1
- **Fact 2** (`log_bayesFactor`): relevance is the differential of conditional
  informativeness, log BF_H(E) = inf(E, ¬H) − inf(E, H)
- **Fact 5** (`bayes_factor_multiplicative_under_cip`): Under CIP,
  BF(A∧B) = BF(A) · BF(B)
- **Theorem 6b** (`xor_not_necessarily_positive`): Counterexample showing
  XOR of two positively relevant propositions can be negatively relevant
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

/-! ### Bayes factor and relevance -/

/-- Bayes factor: P(E∣H) / P(E∣¬H), in `ℝ≥0∞`.

The pre-log ratio that determines relevance sign and magnitude. Total
division gives the boundary cases their true values: P(E∣¬H) = 0 with
P(E∣H) > 0 is `∞` (infinitely strong evidence for H), and 0/0 = 0. -/
noncomputable def bayesFactor (ctx : Context W) (e : Set W) : ℝ≥0∞ :=
  ctx.prior[|ctx.topic] e / ctx.prior[|ctx.topicᶜ] e

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
  simp [bayesFactor, swapIssue, compl_compl]

/-! ### Cross-product characterizations

The relevance signs in real-valued cross-product mass form — the ENNReal→ℝ
transfer done once, edge cases included; the particle files consume these. -/

/-- Positive relevance as a cross-product of real masses: E confirms H iff
the H-side mass of E outweighs its ¬H-side mass after weighting each by the
opposite cell of the issue. -/
theorem posRelevant_iff_real_cross (ctx : Context W) [IsFiniteMeasure ctx.prior]
    {e : Set W} (hH : ctx.prior ctx.topic ≠ 0) (hNH : ctx.prior ctx.topicᶜ ≠ 0) :
    posRelevant ctx e ↔
      (ctx.prior (ctx.topicᶜ ∩ e)).toReal * (ctx.prior ctx.topic).toReal <
      (ctx.prior (ctx.topic ∩ e)).toReal * (ctx.prior ctx.topicᶜ).toReal := by
  have hHm := ctx.topicMeasurable
  have hpH : 0 < (ctx.prior ctx.topic).toReal :=
    ENNReal.toReal_pos hH (measure_ne_top _ _)
  have hpNH : 0 < (ctx.prior ctx.topicᶜ).toReal :=
    ENNReal.toReal_pos hNH (measure_ne_top _ _)
  simp only [posRelevant, bayesFactor]
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
    {e : Set W} (he : ctx.prior e ≠ 0)
    (hH : ctx.prior ctx.topic ≠ 0) (hNH : ctx.prior ctx.topicᶜ ≠ 0) :
    negRelevant ctx e ↔
      (ctx.prior (ctx.topic ∩ e)).toReal * (ctx.prior ctx.topicᶜ).toReal <
      (ctx.prior (ctx.topicᶜ ∩ e)).toReal * (ctx.prior ctx.topic).toReal := by
  have hHm := ctx.topicMeasurable
  have hpH : 0 < (ctx.prior ctx.topic).toReal :=
    ENNReal.toReal_pos hH (measure_ne_top _ _)
  have hpNH : 0 < (ctx.prior ctx.topicᶜ).toReal :=
    ENNReal.toReal_pos hNH (measure_ne_top _ _)
  simp only [negRelevant, bayesFactor]
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

/-! ### The induced binary testing problem

A context induces a binary hypothesis-testing problem in the sense of
mathlib's statistical decision theory (`Mathlib.Probability.Decision`): the
parameter space is `Bool`, each side of the issue generates data from the
prior conditioned on it, and the parameter prior splits the total mass by
the issue. `bayesFactor` is the likelihood ratio of this problem, and
Merin's expected-utility apparatus is its Bayes-risk theory. -/

/-- The data-generating kernel of the induced binary testing problem. -/
noncomputable def Context.hypothesisKernel (ctx : Context W) : Kernel Bool W :=
  .ofFunOfCountable fun h => if h then ctx.prior[|ctx.topic] else ctx.prior[|ctx.topicᶜ]

/-- The parameter prior of the induced binary testing problem. -/
noncomputable def Context.hypothesisPrior (ctx : Context W) : Measure Bool :=
  ctx.prior ctx.topic • Measure.dirac true + ctx.prior ctx.topicᶜ • Measure.dirac false

/-- `bayesFactor` is the likelihood ratio of the induced testing problem. -/
theorem bayesFactor_eq_hypothesisKernel_div (ctx : Context W) (e : Set W) :
    bayesFactor ctx e = ctx.hypothesisKernel true e / ctx.hypothesisKernel false e := rfl

/-! ### Conditional Independence Presumption (CIP) -/

/-- Conditional Independence Presumption (CIP, Merin's Def. 6): A and B are
conditionally independent given both H and ¬H.

P(A∧B∣H) = P(A∣H)·P(B∣H) and P(A∧B∣¬H) = P(A∣¬H)·P(B∣¬H). -/
def CIP (ctx : Context W) (a b : Set W) : Prop :=
  ctx.prior[|ctx.topic] (a ∩ b) =
    ctx.prior[|ctx.topic] a * ctx.prior[|ctx.topic] b ∧
  ctx.prior[|ctx.topicᶜ] (a ∩ b) =
    ctx.prior[|ctx.topicᶜ] a * ctx.prior[|ctx.topicᶜ] b

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
  rw [bayesFactor_swapIssue, bayesFactor,
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
  set x := ctx.prior[|ctx.topic] e with hx
  set y := ctx.prior[|ctx.topicᶜ] e with hy
  rw [bayesFactor_swapIssue, bayesFactor, ← hx, ← hy, div_eq_mul_inv, div_eq_mul_inv,
    mul_mul_mul_comm, mul_comm x y, mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hENotH (hy ▸ cond_apply_ne_top _ ctx.topicMeasurable.compl e),
    ENNReal.mul_inv_cancel hEH (hx ▸ cond_apply_ne_top _ ctx.topicMeasurable e), one_mul]

/-- **Fact 2**: relevance is the differential of conditional
informativeness — log BF_H(E) = inf(E, ¬H) − inf(E, H), where
inf(E, X) = −log P(E∣X) is the conditional surprisal of E. -/
theorem log_bayesFactor (ctx : Context W) [IsFiniteMeasure ctx.prior]
    (e : Set W)
    (hEH : ctx.prior[|ctx.topic] e ≠ 0)
    (hENotH : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    Real.log (bayesFactor ctx e).toReal =
      (-Real.log (ctx.prior[|ctx.topicᶜ] e).toReal) -
      (-Real.log (ctx.prior[|ctx.topic] e).toReal) := by
  rw [bayesFactor, ENNReal.toReal_div,
    Real.log_div (ENNReal.toReal_ne_zero.mpr
        ⟨hEH, cond_apply_ne_top _ ctx.topicMeasurable e⟩)
      (ENNReal.toReal_ne_zero.mpr
        ⟨hENotH, cond_apply_ne_top _ ctx.topicMeasurable.compl e⟩)]
  ring

/-! ### CIP consequences -/

/-- **Fact 5**: Under CIP, the Bayes factor is multiplicative over
conjunction: BF(A∧B) = BF(A) · BF(B) when A and B are conditionally
independent given both H and ¬H. -/
theorem bayes_factor_multiplicative_under_cip (ctx : Context W)
    [IsFiniteMeasure ctx.prior] (a b : Set W)
    (hcip : CIP ctx a b)
    (hNotH' : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    bayesFactor ctx (a ∩ b) = bayesFactor ctx a * bayesFactor ctx b := by
  obtain ⟨hcipH, hcipNH⟩ := hcip
  rw [bayesFactor, bayesFactor, bayesFactor, hcipH, hcipNH,
    ENNReal.mul_div_mul_comm
      (Or.inr (cond_apply_ne_top _ ctx.topicMeasurable.compl b))
      (Or.inr hNotH')]

/-- **Theorem 6a** (part 1): Under CIP with both A, B positively relevant,
conjunction dominates both conjuncts: BF(A∧B) > max(BF(A), BF(B)). -/
theorem conjunction_dominates_conjuncts (ctx : Context W)
    [IsFiniteMeasure ctx.prior] (a b : Set W)
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNotH' : ctx.prior[|ctx.topicᶜ] b ≠ 0)
    (hFinA : bayesFactor ctx a ≠ ∞) (hFinB : bayesFactor ctx b ≠ ∞) :
    max (bayesFactor ctx a) (bayesFactor ctx b) < bayesFactor ctx (a ∩ b) := by
  rw [bayes_factor_multiplicative_under_cip ctx a b hcip hNotH', max_lt_iff]
  constructor
  · calc bayesFactor ctx a = bayesFactor ctx a * 1 := (mul_one _).symm
    _ < bayesFactor ctx a * bayesFactor ctx b :=
        ENNReal.mul_lt_mul_right (pos_of_gt hPosA).ne' hFinA hPosB
  · calc bayesFactor ctx b = 1 * bayesFactor ctx b := (one_mul _).symm
    _ < bayesFactor ctx a * bayesFactor ctx b :=
        ENNReal.mul_lt_mul_left (pos_of_gt hPosB).ne' hFinB hPosA

/-- Arithmetic core for the Theorem 6a disjunction ordering: given four
conditional probabilities satisfying the CIP-derived relationships,
max(pAH/pAnH, pBH/pBnH) exceeds the inclusion-exclusion ratio, which itself
exceeds 1. -/
private lemma max_div_gt_or_div (pAH pBH pAnH pBnH : ℝ)
    (h1 : 0 < pAnH) (h2 : 0 < pBnH)
    (h3 : pAnH < pAH) (h4 : pBnH < pBH)
    (h5 : pAnH < 1) (h6 : pBnH < 1)
    (_h7 : pAH ≤ 1) (h8 : pBH ≤ 1) :
    max (pAH / pAnH) (pBH / pBnH) >
      (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) ∧
    (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) > 1 := by
  have hden_pos : pAnH + pBnH - pAnH * pBnH > 0 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, max_def]; split
    · rename_i hge
      rw [div_lt_div_iff₀ hden_pos h2]
      have h_cross := (div_le_div_iff₀ h1 h2).mp hge
      nlinarith [mul_pos (mul_pos h2 (show (0:ℝ) < pBH by linarith))
        (show pAH - pAnH > 0 from by linarith)]
    · rename_i hlt; push Not at hlt
      rw [div_lt_div_iff₀ hden_pos h1]
      have h_cross := (div_le_div_iff₀ h2 h1).mp (le_of_lt hlt)
      nlinarith [mul_pos (mul_pos h1 (show (0:ℝ) < pAH by linarith))
        (show pBH - pBnH > 0 from by linarith)]
  · rw [gt_iff_lt, one_lt_div hden_pos]
    nlinarith

/-- **Theorem 6a** (full): Under CIP with both A, B positively relevant,
BF(A∧B) > max(BF(A), BF(B)) > BF(A∨B) > 1.

The disjunction ordering rests on inclusion-exclusion for the conditional
measures: P(A∨B∣X) + P(A∧B∣X) = P(A∣X) + P(B∣X). -/
theorem conjunction_dominates_disjunction (ctx : Context W)
    [IsFiniteMeasure ctx.prior] (a b : Set W) (hbm : MeasurableSet b)
    (hcip : CIP ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNotH : ctx.prior[|ctx.topicᶜ] a ≠ 0)
    (hNotH' : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    max (bayesFactor ctx a) (bayesFactor ctx b) < bayesFactor ctx (a ∩ b) ∧
    bayesFactor ctx (a ∪ b) < max (bayesFactor ctx a) (bayesFactor ctx b) ∧
    1 < bayesFactor ctx (a ∪ b) := by
  have hTfin : ∀ e, ctx.prior[|ctx.topic] e ≠ ∞ :=
    cond_apply_ne_top ctx.prior ctx.topicMeasurable
  have hNfin : ∀ e, ctx.prior[|ctx.topicᶜ] e ≠ ∞ :=
    cond_apply_ne_top ctx.prior ctx.topicMeasurable.compl
  have hFinA : bayesFactor ctx a ≠ ∞ := (ENNReal.div_lt_top (hTfin a) hNotH).ne
  have hFinB : bayesFactor ctx b ≠ ∞ := (ENNReal.div_lt_top (hTfin b) hNotH').ne
  refine ⟨conjunction_dominates_conjuncts ctx a b hcip hPosA hPosB hNotH' hFinA hFinB,
    ?_, ?_⟩ <;>
  · -- Real shadows of the four conditional probabilities.
    set pAH := (ctx.prior[|ctx.topic] a).toReal with hpAH
    set pBH := (ctx.prior[|ctx.topic] b).toReal with hpBH
    set pAnH := (ctx.prior[|ctx.topicᶜ] a).toReal with hpAnH
    set pBnH := (ctx.prior[|ctx.topicᶜ] b).toReal with hpBnH
    have hAnH_pos : 0 < pAnH := ENNReal.toReal_pos hNotH (hNfin a)
    have hBnH_pos : 0 < pBnH := ENNReal.toReal_pos hNotH' (hNfin b)
    have hAH_gt : pAnH < pAH := by
      refine (ENNReal.toReal_lt_toReal (hNfin a) (hTfin a)).mpr ?_
      have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hNotH) (Or.inl (hNfin a))).mp hPosA
      rwa [one_mul] at h
    have hBH_gt : pBnH < pBH := by
      refine (ENNReal.toReal_lt_toReal (hNfin b) (hTfin b)).mpr ?_
      have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hNotH') (Or.inl (hNfin b))).mp hPosB
      rwa [one_mul] at h
    have hAH_le : pAH ≤ 1 := by
      rw [hpAH, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (cond_apply_le_one ctx.prior ctx.topicMeasurable a)
    have hBH_le : pBH ≤ 1 := by
      rw [hpBH, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (cond_apply_le_one ctx.prior ctx.topicMeasurable b)
    have harith := max_div_gt_or_div pAH pBH pAnH pBnH hAnH_pos hBnH_pos hAH_gt hBH_gt
      (lt_of_lt_of_le hAH_gt hAH_le) (lt_of_lt_of_le hBH_gt hBH_le) hAH_le hBH_le
    -- Inclusion-exclusion under both conditionals, CIP-substituted, in ℝ.
    have hOrH : (ctx.prior[|ctx.topic] (a ∪ b)).toReal = pAH + pBH - pAH * pBH := by
      have h := congrArg ENNReal.toReal (measure_union_add_inter (μ := ctx.prior[|ctx.topic]) a hbm)
      rw [ENNReal.toReal_add (hTfin _) (hTfin _), ENNReal.toReal_add (hTfin _) (hTfin _),
        hcip.1, ENNReal.toReal_mul] at h
      linarith
    have hOrNH : (ctx.prior[|ctx.topicᶜ] (a ∪ b)).toReal = pAnH + pBnH - pAnH * pBnH := by
      have h := congrArg ENNReal.toReal
        (measure_union_add_inter (μ := ctx.prior[|ctx.topicᶜ]) a hbm)
      rw [ENNReal.toReal_add (hNfin _) (hNfin _), ENNReal.toReal_add (hNfin _) (hNfin _),
        hcip.2, ENNReal.toReal_mul] at h
      linarith
    have hOrNH_ne : ctx.prior[|ctx.topicᶜ] (a ∪ b) ≠ 0 := fun h0 =>
      hNotH (measure_mono_null Set.subset_union_left h0)
    have hFinOr : bayesFactor ctx (a ∪ b) ≠ ∞ := (ENNReal.div_lt_top (hTfin _) hOrNH_ne).ne
    have hBFOr : (bayesFactor ctx (a ∪ b)).toReal =
        (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) := by
      rw [bayesFactor, ENNReal.toReal_div, hOrH, hOrNH]
    first
    | -- BF(A∨B) < max(BF(A), BF(B))
      refine (ENNReal.toReal_lt_toReal hFinOr (by simp [hFinA, hFinB])).mp ?_
      rw [hBFOr, ENNReal.toReal_max hFinA hFinB, bayesFactor, bayesFactor,
        ENNReal.toReal_div, ENNReal.toReal_div]
      exact harith.1
    | -- 1 < BF(A∨B)
      refine (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hFinOr).mp ?_
      rw [hBFOr, ENNReal.toReal_one]
      exact harith.2

/-! ### The Bayesian bridge -/

/-- Probabilistic support implies DTS positive relevance for binary issues.
The Bayes-theorem bridge: P(E∣H) > P(E) ⟹ BF_H(E) > 1.

The edge case P(E ∩ ¬H) = 0 needs no special treatment: the Bayes factor is
then genuinely infinite.

Promoted from the IKW2025 Part II "Bayesian-to-DTS bridge" in 0.230.502 —
pure DTS-internal content (no IKW dependency), belongs in DTS Core. -/
theorem probSupports_implies_posRelevant_binary
    (μ : Measure W) [IsProbabilityMeasure μ] {topic : Set W}
    (htopic : MeasurableSet topic) (evidence : Set W)
    (hH_pos : μ topic ≠ 0) (hNH_pos : μ topicᶜ ≠ 0)
    (hSupp : μ evidence < μ[|topic] evidence) :
    posRelevant ⟨topic, htopic, μ⟩ evidence := by
  have hpart : μ (evidence ∩ topic) + μ (evidence ∩ topicᶜ) = μ evidence := by
    simpa [Set.sdiff_eq] using measure_inter_add_sdiff evidence htopic
  have hEH : μ[|topic] evidence = (μ topic)⁻¹ * μ (topic ∩ evidence) :=
    cond_apply htopic μ evidence
  unfold posRelevant bayesFactor
  rcases eq_or_ne (μ[|topicᶜ] evidence) 0 with hz | hz
  · -- P(E∣¬H) = 0: the factor is ∞ once P(E∣H) > 0.
    have hnum : μ[|topic] evidence ≠ 0 := by
      intro h0
      rw [h0] at hSupp
      exact absurd hSupp (by simp)
    rw [hz, ENNReal.div_zero hnum]
    exact ENNReal.one_lt_top
  · -- Main case: cross-multiply in ℝ.
    have hENH : μ[|topicᶜ] evidence = (μ topicᶜ)⁻¹ * μ (topicᶜ ∩ evidence) :=
      cond_apply htopic.compl μ evidence
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hz)
      (Or.inl (cond_apply_ne_top μ htopic.compl evidence)), one_mul]
    -- Convert to real arithmetic.
    have hHfin := measure_ne_top μ topic
    have hNHfin := measure_ne_top μ topicᶜ
    have hsum1 : μ topic + μ topicᶜ = 1 := prob_add_prob_compl htopic
    set pH := (μ topic).toReal with hpH
    set pNH := (μ topicᶜ).toReal with hpNH
    set pEH := (μ (topic ∩ evidence)).toReal with hpEH
    set pENH := (μ (topicᶜ ∩ evidence)).toReal with hpENH
    have hpH_pos : 0 < pH := ENNReal.toReal_pos hH_pos hHfin
    have hpNH_pos : 0 < pNH := ENNReal.toReal_pos hNH_pos hNHfin
    have hpEH_nonneg : 0 ≤ pEH := ENNReal.toReal_nonneg
    have hpENH_nonneg : 0 ≤ pENH := ENNReal.toReal_nonneg
    have hsum1' : pH + pNH = 1 := by
      rw [hpH, hpNH, ← ENNReal.toReal_add hHfin hNHfin, hsum1, ENNReal.toReal_one]
    have hpartR : pEH + pENH = (μ evidence).toReal := by
      rw [hpEH, hpENH, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      congr 1
      simpa [Set.inter_comm] using hpart
    have hSuppR : (μ evidence).toReal < pEH / pH := by
      have := ENNReal.toReal_lt_toReal (measure_ne_top μ evidence)
        (cond_apply_ne_top μ htopic evidence) |>.mpr hSupp
      rwa [hEH, ENNReal.toReal_mul, ENNReal.toReal_inv, inv_mul_eq_div] at this
    refine ENNReal.toReal_lt_toReal
      (cond_apply_ne_top μ htopic.compl evidence)
      (cond_apply_ne_top μ htopic evidence) |>.mp ?_
    rw [hEH, hENH, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_inv, inv_mul_eq_div, inv_mul_eq_div, div_lt_div_iff₀ hpNH_pos hpH_pos]
    nlinarith [hSuppR, hsum1', hpartR, mul_pos hpH_pos hpNH_pos,
      (lt_div_iff₀ hpH_pos).mp hSuppR]

/-- Negative relevance (DTS) implies non-support (probabilistic).

Contrapositive of `probSupports_implies_posRelevant_binary`. Promoted from
IKW2025 Part II in 0.230.502. -/
theorem negRelevant_implies_not_probSupports
    (μ : Measure W) [IsProbabilityMeasure μ] {topic : Set W}
    (htopic : MeasurableSet topic) (evidence : Set W)
    (hH_pos : μ topic ≠ 0) (hNH_pos : μ topicᶜ ≠ 0)
    (hNeg : negRelevant ⟨topic, htopic, μ⟩ evidence) :
    ¬ μ evidence < μ[|topic] evidence := fun hSupp =>
  absurd (probSupports_implies_posRelevant_binary μ htopic evidence
    hH_pos hNH_pos hSupp) (lt_asymm hNeg)

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
    simp only [posRelevant, bayesFactor, cond_apply MeasurableSet.of_discrete,
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

end DTS

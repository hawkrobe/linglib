import Linglib.Semantics.Degree.Gradability.Aggregation
import Linglib.Core.Probability.Posterior
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod

/-!
# [waldon-etal-2023]

Waldon, B., Condoravdi, C., Levin, B., & Degen, J. (2023). On the context
dependence of artifact noun interpretation. In *Proceedings of Sinn und
Bedeutung 27*, pp. 674–692.

## Key Claims

1. **Goal Sensitivity**: policy goals systematically modulate artifact noun
   category boundaries. A flashlight is more likely to count as an
   "electronic device" when the goal is limiting distracting light than
   when it's limiting noise.

2. **Multi-dimensional degree semantics for artifact nouns** (eq. 8):
   ⟦vehicle⟧ = λx. Σ_{f ∈ **F**(vehicle)} f(x) · **W**(vehicle, f)
   where **F** returns context-relevant measure functions and **W** weights
   them. Artifact nouns compose additively ([sassoon-fadlon-2017]),
   in contrast to natural kinds which compose multiplicatively.

   This is the `weightedScore` substrate primitive in
   `Semantics/Degree/Aggregation.lean`. Tham 2025 adds a
   third aggregation mode (`spatialNormalizedScore`, with a host-extent
   denominator) for physical disturbance predicates — see
   `Studies/Tham2025.lean §15` for the
   substrate-level contrast (Waldon's domain has no host-extent
   denominator naturally; Tham's does).

3. **Interpretive model** (§4.2, the paper's implemented version per its
   own simplifying assumptions): a literal Bayesian update over each
   object's prohibition status. The threshold `s` is uniform on [0, 1]
   and marginalised analytically; `F`/`W` are fixed per condition; the
   prohibition prior is 1/2. The marginal posterior that `o` is
   prohibited then *equals the goal-weighted measure* `m(o)`
   (`prohibitionPosterior_eq_measure`), so every behavioural prediction
   reduces to a measure comparison.

4. **Goal Sensitive vs. Goal Insensitive** (§4.3): the single free
   parameter γ weights the context-independent `cat` dimension against
   the goal-relevant dimensions. γ = 1 is the Goal Insensitive null —
   provably condition-independent (`goal_insensitive_at_one`) — while
   every qualitative prediction below holds for *all* γ < 1; the BDA
   maximum-likelihood estimate is γ = 0.758 (95% CrI [0.756, 0.758]).

## Model

    m_g(o)  = γ·cat(o) + (1−γ)·f_g(o)                      (eq. 13)
    m_B(o)  = γ·cat(o) + (1−γ)·Σ_g p(g)·f_g(o)             (eq. 14)
    P(o prohibited | rule) = m(o)                           (eq. 12, fn. 20-21)

where `cat` is the category-membership measure, `f_g` the goal-relevant
feature measures, and `p` the goal-plausibility function. Both measure
forms are `weightedScore` instances ([sassoon-fadlon-2017] additive
aggregation).
-/

namespace WaldonEtAl2023

open Degree.Aggregation

-- ════════════════════════════════════════════════════
-- § 1. Domain Types
-- ════════════════════════════════════════════════════

/-- Objects in the "No electronic devices" scenario (Fig. 1). -/
inductive Object where
  | candle      -- clear non-member
  | flashlight  -- edge case
  | boombox     -- clear member
  | tablet      -- clear member
  deriving Repr, DecidableEq, Fintype

/-- The signaler's policy goals (Appendix A). -/
inductive Goal where
  | limitLight         -- "emit light that could distract..."
  | limitNoise         -- "create noise that could distract..."
  | preventRecordings  -- "record performances and distribute..."
  deriving Repr, DecidableEq, Fintype

/-- Experimental conditions (determines latentPrior over Goals). -/
inductive GoalCondition where
  | neutral            -- no goal stated; prior spread across goals
  | limitLight         -- goal = limitLight; prior concentrated
  | limitNoise
  | preventRecordings
  deriving Repr, DecidableEq, Fintype

-- ════════════════════════════════════════════════════
-- § 2. Feature Scores (Schematic)
-- ════════════════════════════════════════════════════

/-! **These values are schematic approximations, not from the paper's
    actual norming data.** The paper parameterizes the feature measures
    `f_g(o)`, the category measure `cat(o)`, and the goal plausibilities
    `p(g)` via separate norming studies (feature attribution, category
    membership, and goal plausibility, §3.1). The actual values are
    available at the OSF links cited in the paper. The values below
    capture the qualitative pattern described in the paper (flashlights
    emit light but not noise; boomboxes emit noise but not light; etc.);
    the prediction theorems in §5 are additionally γ-generic, so no
    fitted parameter value is assumed. -/

/-- Goal-relevant feature measures — the components of the paper's eq. (8),
parameterised in the paper by the feature-attribution norming study. -/
def emitLight : Object → ℚ
  | .candle => 7/10 | .flashlight => 9/10 | .boombox => 1/10 | .tablet => 6/10

def emitNoise : Object → ℚ
  | .candle => 1/20 | .flashlight => 1/20 | .boombox => 9/10 | .tablet => 3/10

def canRecord : Object → ℚ
  | .candle => 1/20 | .flashlight => 1/20 | .boombox => 1/20 | .tablet => 9/10

/-- The feature measure a policy goal makes relevant (eq. 13). -/
def goalFeature : Goal → Object → ℚ
  | .limitLight => emitLight
  | .limitNoise => emitNoise
  | .preventRecordings => canRecord

/-- `cat`: the context-independent category-membership measure (the paper's
`cat^{elec.device}`, from the category-membership norming study). -/
def cat : Object → ℚ
  | .candle     => 1/20   -- clearly not electronic
  | .flashlight => 1/2    -- edge case (~0.5 norming)
  | .boombox    => 19/20  -- clearly electronic
  | .tablet     => 19/20  -- clearly electronic

theorem cat_pos : ∀ o : Object, 0 < cat o := by
  intro o; cases o <;> norm_num [cat]

/-- Goal-plausibility function `p` for the goal-neutral condition (eq. 14,
fn. 22: values from the goal-plausibility norming, summing to 1 over the
three goals; uniform here, schematically). -/
def plausibility : Goal → ℚ := fun _ => 1/3

-- ════════════════════════════════════════════════════
-- § 3. The Goal-Weighted Measure (eqs. 8, 13, 14)
-- ════════════════════════════════════════════════════

/-- The context-sensitive measure `⟦electronic device⟧^{F,W}` under each
experimental condition (eqs. 13–14): a `weightedScore` over the `cat`
dimension (weight γ) and the goal-relevant dimensions (weight 1−γ,
plausibility-split in the goal-neutral condition). -/
def deviceMeasure (γ : ℚ) : GoalCondition → Object → ℚ
  | .neutral => weightedScore
      (γ :: [Goal.limitLight, .limitNoise, .preventRecordings].map
        fun g => (1 - γ) * plausibility g)
      (cat :: [Goal.limitLight, .limitNoise, .preventRecordings].map goalFeature)
  | .limitLight        => weightedScore [γ, 1 - γ] [cat, emitLight]
  | .limitNoise        => weightedScore [γ, 1 - γ] [cat, emitNoise]
  | .preventRecordings => weightedScore [γ, 1 - γ] [cat, canRecord]

/-- Closed form for the explicit-goal conditions (eq. 13). -/
theorem deviceMeasure_limitLight (γ : ℚ) (o : Object) :
    deviceMeasure γ .limitLight o = γ * cat o + (1 - γ) * emitLight o := by
  simp [deviceMeasure, weightedScore]

theorem deviceMeasure_limitNoise (γ : ℚ) (o : Object) :
    deviceMeasure γ .limitNoise o = γ * cat o + (1 - γ) * emitNoise o := by
  simp [deviceMeasure, weightedScore]

theorem deviceMeasure_preventRecordings (γ : ℚ) (o : Object) :
    deviceMeasure γ .preventRecordings o = γ * cat o + (1 - γ) * canRecord o := by
  simp [deviceMeasure, weightedScore]

/-- Closed form for the goal-neutral condition (eq. 14): the goal weight is
split by plausibility. -/
theorem deviceMeasure_neutral (γ : ℚ) (o : Object) :
    deviceMeasure γ .neutral o
      = γ * cat o + (1 - γ) * (plausibility .limitLight * emitLight o
          + plausibility .limitNoise * emitNoise o
          + plausibility .preventRecordings * canRecord o) := by
  simp [deviceMeasure, weightedScore, goalFeature]
  ring

/-- The measure stays in [0, 1] for γ ∈ [0, 1] — the domain on which the
threshold semantics reads it as a probability. -/
theorem deviceMeasure_mem_Icc {γ : ℚ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (c : GoalCondition) (o : Object) :
    deviceMeasure γ c o ∈ Set.Icc (0 : ℚ) 1 := by
  constructor <;>
    (cases c <;> cases o <;>
      simp [deviceMeasure, weightedScore, goalFeature, cat, emitLight, emitNoise,
        canRecord, plausibility] <;>
      nlinarith)

-- ════════════════════════════════════════════════════
-- § 4. The Interpretive Model (eq. 12)
-- ════════════════════════════════════════════════════

open scoped ENNReal

/-- Probability that an object meets the standard: the threshold `s` is
uniform on [0, 1] (fn. 20), so `P(pos^s(o) = 1) = P(s ≤ m(o))` is the
Lebesgue mass of `[0, m]`. -/
noncomputable def posProb (m : ℚ) : ℝ≥0∞ :=
  MeasureTheory.volume (Set.Icc (0 : ℝ) (m : ℝ))

theorem posProb_eq (m : ℚ) : posProb m = ENNReal.ofReal (m : ℝ) := by
  rw [posProb, Real.volume_Icc, sub_zero]

/-- Eq. (12) under the paper's implementation assumptions (fn. 21): the joint
posterior weight of a prohibition status is the threshold-marginalised
standard-meeting indicator times the uniform prohibition prior. -/
noncomputable def ruleUpdateWeight (m : ℚ) : Bool → ℝ≥0∞
  | true  => 2⁻¹ * posProb m
  | false => 2⁻¹ * (1 - posProb m)

private theorem ruleUpdateWeight_tsum_ne_zero (m : ℚ) :
    (∑' b, ruleUpdateWeight m b) ≠ 0 := by
  rw [tsum_bool]
  intro h
  obtain ⟨hf, ht⟩ := add_eq_zero.mp h
  rcases mul_eq_zero.mp hf with h2 | h2
  · exact (ENNReal.inv_ne_zero.mpr (by norm_num)) h2
  · rcases mul_eq_zero.mp ht with h3 | h3
    · exact (ENNReal.inv_ne_zero.mpr (by norm_num)) h3
    · rw [h3, tsub_zero] at h2
      exact one_ne_zero h2

private theorem ruleUpdateWeight_tsum_ne_top (m : ℚ) :
    (∑' b, ruleUpdateWeight m b) ≠ ⊤ := by
  rw [tsum_bool]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · exact ENNReal.mul_ne_top (by norm_num)
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  · exact ENNReal.mul_ne_top (by norm_num)
      (by rw [posProb_eq]; exact ENNReal.ofReal_ne_top)

/-- The listener's posterior over an object's prohibition status after
observing the rule (eq. 12, marginalised over the uniform threshold). -/
noncomputable def prohibitionPMF (m : ℚ) : PMF Bool :=
  PMF.normalize (ruleUpdateWeight m)
    (ruleUpdateWeight_tsum_ne_zero m) (ruleUpdateWeight_tsum_ne_top m)

/-- Marginal posterior probability that `o` is prohibited in condition `c`
(the `L^γ(o prohibited | rule)` of eq. 15c). -/
noncomputable def prohibitionPosterior (γ : ℚ) (c : GoalCondition) (o : Object) : ℝ≥0∞ :=
  prohibitionPMF (deviceMeasure γ c o) true

/-- **The posterior is the measure** (fns. 20–21): with the threshold uniform
on [0, 1] and a 1/2 prohibition prior, the marginal posterior probability of
prohibition collapses to the goal-weighted measure itself. Every behavioural
prediction below is therefore a measure comparison. -/
theorem prohibitionPMF_eq_measure {m : ℚ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    prohibitionPMF m true = ENNReal.ofReal (m : ℝ) := by
  have hsum : (∑' b, ruleUpdateWeight m b) = 2⁻¹ := by
    rw [tsum_bool, ruleUpdateWeight, ruleUpdateWeight, posProb_eq,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by exact_mod_cast h0),
      ← mul_add,
      ← ENNReal.ofReal_add (by norm_num; exact_mod_cast h1) (by exact_mod_cast h0)]
    norm_num
  rw [prohibitionPMF, PMF.normalize_apply, hsum, ruleUpdateWeight, posProb_eq,
    inv_inv, mul_right_comm, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
    one_mul]

theorem prohibitionPosterior_eq_measure {γ : ℚ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (c : GoalCondition) (o : Object) :
    prohibitionPosterior γ c o = ENNReal.ofReal (deviceMeasure γ c o : ℝ) :=
  prohibitionPMF_eq_measure (deviceMeasure_mem_Icc h0 h1 c o).1
    (deviceMeasure_mem_Icc h0 h1 c o).2

-- ════════════════════════════════════════════════════
-- § 5. Prediction Theorems (γ-generic)
-- ════════════════════════════════════════════════════

/-! Every prediction holds for **all** γ ∈ [0, 1) — the entire Goal
Sensitive regime — via `prohibitionPosterior_eq_measure` plus rational
arithmetic on the measures. The proofs need no fitted parameter value. -/

private theorem posterior_lt_posterior {γ : ℚ} (h0 : 0 ≤ γ) (h1 : γ < 1)
    {c c' : GoalCondition} {o o' : Object}
    (key : deviceMeasure γ c o < deviceMeasure γ c' o') :
    prohibitionPosterior γ c o < prohibitionPosterior γ c' o' := by
  rw [prohibitionPosterior_eq_measure h0 h1.le,
    prohibitionPosterior_eq_measure h0 h1.le, ENNReal.ofReal_lt_ofReal_iff]
  · exact_mod_cast key
  · exact_mod_cast lt_of_le_of_lt (deviceMeasure_mem_Icc h0 h1.le c o).1 key

section Predictions

variable {γ : ℚ}

/-- Under limitLight, the flashlight (edge case) is more likely prohibited
    than the candle (clear non-member): both `cat` and `emit-light` favour it. -/
theorem limitLight_flashlight_gt_candle (h0 : 0 ≤ γ) (h1 : γ < 1) :
    prohibitionPosterior γ .limitLight .flashlight >
    prohibitionPosterior γ .limitLight .candle :=
  posterior_lt_posterior h0 h1 (by
    rw [deviceMeasure_limitLight, deviceMeasure_limitLight]
    simp only [cat, emitLight]
    linarith)

/-- Under limitNoise, the boombox is the primary target. -/
theorem limitNoise_boombox_gt_flashlight (h0 : 0 ≤ γ) (h1 : γ < 1) :
    prohibitionPosterior γ .limitNoise .boombox >
    prohibitionPosterior γ .limitNoise .flashlight :=
  posterior_lt_posterior h0 h1 (by
    rw [deviceMeasure_limitNoise, deviceMeasure_limitNoise]
    simp only [cat, emitNoise]
    linarith)

/-- Under limitLight, the tablet (clear member + emits light) outranks the
    boombox (clear member, no light): the `cat` dimension ties, so the goal
    dimension decides — strict only in the Goal Sensitive regime γ < 1. -/
theorem limitLight_tablet_gt_boombox (h0 : 0 ≤ γ) (h1 : γ < 1) :
    prohibitionPosterior γ .limitLight .tablet >
    prohibitionPosterior γ .limitLight .boombox :=
  posterior_lt_posterior h0 h1 (by
    rw [deviceMeasure_limitLight, deviceMeasure_limitLight]
    simp only [cat, emitLight]
    linarith)

/-- **Goal sensitivity for flashlights** (the paper's key result, Fig. 1):
    the flashlight is more likely prohibited under limitLight than limitNoise
    — the measure difference is `(1−γ)·(emitLight − emitNoise)(flashlight)`,
    positive exactly when γ < 1. -/
theorem goal_sensitivity_flashlight (h0 : 0 ≤ γ) (h1 : γ < 1) :
    prohibitionPosterior γ .limitLight .flashlight >
    prohibitionPosterior γ .limitNoise .flashlight :=
  posterior_lt_posterior h0 h1 (by
    rw [deviceMeasure_limitLight, deviceMeasure_limitNoise]
    simp only [cat, emitLight, emitNoise]
    linarith)

/-- **Goal sensitivity for boomboxes** (reverse pattern, Fig. 1). -/
theorem goal_sensitivity_boombox (h0 : 0 ≤ γ) (h1 : γ < 1) :
    prohibitionPosterior γ .limitNoise .boombox >
    prohibitionPosterior γ .limitLight .boombox :=
  posterior_lt_posterior h0 h1 (by
    rw [deviceMeasure_limitLight, deviceMeasure_limitNoise]
    simp only [cat, emitLight, emitNoise]
    linarith)

/-- **Goal sensitivity for tablets** under preventRecordings vs limitNoise. -/
theorem goal_sensitivity_tablet (h0 : 0 ≤ γ) (h1 : γ < 1) :
    prohibitionPosterior γ .preventRecordings .tablet >
    prohibitionPosterior γ .limitNoise .tablet :=
  posterior_lt_posterior h0 h1 (by
    rw [deviceMeasure_preventRecordings, deviceMeasure_limitNoise]
    simp only [cat, emitNoise, canRecord]
    linarith)

/-- **No single threshold shift explains the goal effect** (the paper's
    argument against a purely context-shifted standard, pp. 681–682): relative
    to the goal-neutral baseline, the limitLight goal *raises* the flashlight
    and simultaneously *lowers* the boombox. A shifted threshold θ_B moves all
    objects the same direction; goal-sensitive dimension weights do not. -/
theorem light_goal_bidirectional (h0 : 0 ≤ γ) (h1 : γ < 1) :
    prohibitionPosterior γ .limitLight .flashlight >
      prohibitionPosterior γ .neutral .flashlight ∧
    prohibitionPosterior γ .limitLight .boombox <
      prohibitionPosterior γ .neutral .boombox :=
  ⟨posterior_lt_posterior h0 h1 (by
      rw [deviceMeasure_limitLight, deviceMeasure_neutral]
      simp only [cat, emitLight, emitNoise, canRecord, plausibility]
      linarith),
   posterior_lt_posterior h0 h1 (by
      rw [deviceMeasure_limitLight, deviceMeasure_neutral]
      simp only [cat, emitLight, emitNoise, canRecord, plausibility]
      linarith)⟩

end Predictions

/-- **The Goal Insensitive null** (γ = 1): the measure ignores the goal
dimensions entirely, so no condition manipulation can move any object's
posterior. The experiment's Bayesian model comparison rejects this value
(γ̂ = 0.758, 95% CrI [0.756, 0.758], §4.3). -/
theorem goal_insensitive_at_one (c c' : GoalCondition) (o : Object) :
    deviceMeasure 1 c o = deviceMeasure 1 c' o := by
  cases c <;> cases c' <;>
    simp [deviceMeasure, weightedScore, goalFeature]

/-- The BDA maximum-likelihood estimate of γ (§4.3). Strictly inside the Goal
Sensitive regime, so every prediction theorem above applies to it. -/
def fittedGamma : ℚ := 758/1000

theorem fittedGamma_goal_sensitive : 0 ≤ fittedGamma ∧ fittedGamma < 1 := by
  constructor <;> norm_num [fittedGamma]

/-- The flashlight's goal-relevant feature is much stronger under limitLight
    than limitNoise — the driver of `goal_sensitivity_flashlight`. -/
theorem flashlight_light_gt_noise :
    emitLight .flashlight > emitNoise .flashlight := by
  norm_num [emitLight, emitNoise]

/-- The boombox's pattern reverses — the driver of `goal_sensitivity_boombox`. -/
theorem boombox_noise_gt_light :
    emitNoise .boombox > emitLight .boombox := by
  norm_num [emitLight, emitNoise]

-- ════════════════════════════════════════════════════
-- § 6. Additive vs. Multiplicative Composition
-- ════════════════════════════════════════════════════

/-! [sassoon-fadlon-2017] contrast artifact nouns (additive: Σ)
    with natural kinds (multiplicative: Π). Under multiplicative
    composition, a zero on ANY dimension kills membership. Under
    additive, other dimensions compensate. -/

/-- All feature measures as a list (for aggregation functions). -/
def allFeatures : List (Object → ℚ) := [emitLight, emitNoise, canRecord]

/-- Under multiplicative composition, the flashlight gets ZERO because
    emitNoise(flashlight) = canRecord(flashlight) = 1/20 ≈ 0. The
    product is negligibly small. -/
theorem flashlight_multiplicative_negligible :
    multiplicativeScore allFeatures .flashlight < 1/100 := by native_decide

/-- Under additive composition, the flashlight gets a positive score
    despite near-zero on noise/recording — emitLight compensates. -/
theorem flashlight_additive_positive :
    weightedScore [1, 1, 1] allFeatures .flashlight > 1/2 := by native_decide

/-- Artifact noun aggregation is utilitarian, not counting — the same
    point made by [dambrosio-hedden-2024] for multidimensional
    adjectives. [sassoon-2013]'s binding types (conjunctive,
    disjunctive, mixed) are all counting aggregation and cannot
    capture the weighted, continuous-measure structure of artifact
    noun interpretation. -/
theorem artifact_aggregation_is_utilitarian :
    AggregationType.utilitarian ≠ .counting := by decide

end WaldonEtAl2023

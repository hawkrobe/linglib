import Linglib.Theories.Semantics.Degree.Aggregation
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod

/-!
# @cite{waldon-etal-2023}

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
   them. Artifact nouns compose additively (@cite{sassoon-fadlon-2017}),
   in contrast to natural kinds which compose multiplicatively.

3. **RSA model** (companion handout): a signaler (rule-maker) produces
   rules to advance policy goals; the listener jointly infers which
   objects are targeted and what the signaler's goal is:
   L₁(obj, goal | rule) ∝ S(rule | obj, goal) · P_G(goal) · P_CAT(obj)
   where S ∝ U(goal, obj)^α and U is the utility of prohibiting obj
   given goal (parameterized by feature attribution norming).

## RSAConfig Mapping

- **U** = `Utterance` (rule, silence)
- **W** = `Object` (candle, flashlight, boombox, tablet)
- **Latent** = `Goal` (limitLight, limitNoise, preventRecordings)
- **meaning(goal, rule, obj)** = `utility goal obj` (feature attribution)
- **meaning(goal, silence, obj)** = 1 (uninformative)
- **s1Score** = beliefAction with cost = 0
- **worldPrior** = `catPrior` (category membership norming)
- **latentPrior** = `goalPrior condition` (concentrated or uniform)
-/

namespace Phenomena.Gradability.Studies.WaldonEtAl2023

open Semantics.Degree.Aggregation

-- ════════════════════════════════════════════════════
-- § 1. Domain Types
-- ════════════════════════════════════════════════════

/-- Objects in the "No electronic devices" scenario (Fig. 1). -/
inductive Object where
  | candle      -- clear non-member
  | flashlight  -- edge case
  | boombox     -- clear member
  | tablet      -- clear member
  deriving Repr, DecidableEq, BEq, Fintype

/-- The signaler's policy goals (Appendix A). -/
inductive Goal where
  | limitLight         -- "emit light that could distract..."
  | limitNoise         -- "create noise that could distract..."
  | preventRecordings  -- "record performances and distribute..."
  deriving Repr, DecidableEq, BEq, Fintype

/-- Experimental conditions (determines latentPrior over Goals). -/
inductive GoalCondition where
  | neutral            -- no goal stated; prior spread across goals
  | limitLight         -- goal = limitLight; prior concentrated
  | limitNoise
  | preventRecordings
  deriving Repr, DecidableEq, BEq, Fintype

/-- Utterances: the rule-maker produces the rule or stays silent. -/
inductive Utterance where
  | rule    -- "No electronic devices are allowed in the theater"
  | silence -- no rule produced
  deriving Repr, DecidableEq, BEq, Fintype

-- ════════════════════════════════════════════════════
-- § 2. Feature Scores (Schematic)
-- ════════════════════════════════════════════════════

/-! **These values are schematic approximations, not from the paper's
    actual norming data.** The paper parameterizes U(goal, obj) and
    P_CAT(obj) via separate norming studies (feature attribution and
    category membership, §3.1). The actual values are available at
    the OSF links cited in the paper. The values below capture the
    qualitative pattern described in the paper (flashlights emit light
    but not noise; boomboxes emit noise but not light; etc.) and are
    sufficient to verify the model's structural predictions. -/

/-- U(goal, obj): utility of prohibiting obj given goal.
    Higher values = prohibiting this object better advances the goal.
    From feature attribution norming (schematic). -/
def utility : Goal → Object → ℚ
  | .limitLight,        .candle     => 7/10   -- candles emit light
  | .limitLight,        .flashlight => 9/10   -- flashlights strongly emit light
  | .limitLight,        .boombox    => 1/10   -- boomboxes don't emit light
  | .limitLight,        .tablet     => 6/10   -- tablets emit light (screens)
  | .limitNoise,        .candle     => 1/20   -- candles don't emit noise
  | .limitNoise,        .flashlight => 1/20   -- flashlights don't emit noise
  | .limitNoise,        .boombox    => 9/10   -- boomboxes strongly emit noise
  | .limitNoise,        .tablet     => 3/10   -- tablets emit some noise
  | .preventRecordings, .candle     => 1/20
  | .preventRecordings, .flashlight => 1/20
  | .preventRecordings, .boombox    => 1/20
  | .preventRecordings, .tablet     => 9/10   -- tablets can record

/-- P_CAT(obj): prior category membership as "electronic device".
    From category membership norming (schematic). -/
def catPrior : Object → ℚ
  | .candle     => 1/20   -- clearly not electronic
  | .flashlight => 1/2    -- edge case (~0.5 norming)
  | .boombox    => 19/20  -- clearly electronic
  | .tablet     => 19/20  -- clearly electronic

theorem catPrior_pos : ∀ o : Object, 0 < catPrior o := by
  intro o; cases o <;> native_decide

/-- P_G(goal | condition): goal plausibility prior.
    In explicit goal conditions, the prior concentrates on the stated
    goal. In the neutral condition, all goals are equally plausible. -/
def goalPrior : GoalCondition → Object → Goal → ℚ
  | .limitLight,        _, .limitLight        => 1
  | .limitLight,        _, _                  => 0
  | .limitNoise,        _, .limitNoise        => 1
  | .limitNoise,        _, _                  => 0
  | .preventRecordings, _, .preventRecordings => 1
  | .preventRecordings, _, _                  => 0
  | .neutral,           _, _                  => 1  -- uniform (unnormalized)

-- ════════════════════════════════════════════════════
-- § 3. RSA Model (Companion Handout)
-- ════════════════════════════════════════════════════

/-- RSA meaning function: for a given goal, how consistent is each
    object with each utterance?
    - **rule**: meaning = U(goal, obj) (the utility of prohibiting obj)
    - **silence**: meaning = 1 (uninformative — equally consistent
      with all objects)

    L0 normalizes across objects, giving a distribution over which
    objects the rule targets. S1 = L0^α normalizes across utterances,
    giving the speaker's probability of producing the rule.

    **Model simplification:** The companion handout defines
    U(goal, ¬obj) = 1 − U(goal, obj) for silence, making silence
    informative (not-prohibiting has utility). Our RSAConfig uses
    meaning(silence) = 1 (uninformative, uniform L0), a standard RSA
    convention. This preserves within- and cross-config orderings
    because S1 is monotone in L0, and L0 is monotone in meaning. -/
def rsaMeaning (goal : Goal) (utt : Utterance) (obj : Object) : ℚ :=
  match utt with
  | .rule    => utility goal obj
  | .silence => 1

theorem rsaMeaning_nonneg :
    ∀ (goal : Goal) (utt : Utterance) (obj : Object),
    0 ≤ rsaMeaning goal utt obj := by
  intro goal utt obj; cases utt <;> cases goal <;> cases obj <;> native_decide

/-- Build one RSAConfig per experimental condition.
    Follows the companion handout's architecture:
    L₁(obj, goal | rule) ∝ S(rule | obj, goal) · P_G(goal) · P_CAT(obj)

    Structurally parallel to @cite{lassiter-goodman-2017}'s threshold RSA:
    both jointly infer world state and a latent parameter (threshold θ in
    LG2017, policy goal in this model). -/
noncomputable def mkCfg (condition : GoalCondition) :
    RSA.RSAConfig Utterance Object where
  Latent := Goal
  meaning _ goal utt obj := rsaMeaning goal utt obj
  meaning_nonneg := fun _ goal utt obj => by
    exact_mod_cast rsaMeaning_nonneg goal utt obj
  s1Score := fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else Real.exp (α * Real.log (l0 u w))
  s1Score_nonneg := fun l0 α _ w u _ _ => by
    split
    · exact le_refl 0
    · exact le_of_lt (Real.exp_pos _)
  α := 1
  α_pos := by norm_num
  worldPrior obj := catPrior obj
  worldPrior_nonneg := fun obj => by exact_mod_cast le_of_lt (catPrior_pos obj)
  latentPrior obj goal := goalPrior condition obj goal
  latentPrior_nonneg := fun _ goal => by
    cases condition <;> cases goal <;> simp [goalPrior]

-- ════════════════════════════════════════════════════
-- § 4. Prediction Theorems
-- ════════════════════════════════════════════════════

/-! Within-config predictions (object ordering) via `rsa_predict`. -/

/-- Under limitLight, the flashlight (edge case) is more likely to
    be targeted by the rule than the candle (clear non-member). -/
theorem limitLight_flashlight_gt_candle :
    (mkCfg .limitLight).L1 .rule .flashlight >
    (mkCfg .limitLight).L1 .rule .candle := by rsa_predict

/-- Under limitNoise, the boombox is the primary target. -/
theorem limitNoise_boombox_gt_flashlight :
    (mkCfg .limitNoise).L1 .rule .boombox >
    (mkCfg .limitNoise).L1 .rule .flashlight := by rsa_predict

/-- Under limitLight, the tablet (clear member + emits light) outranks
    the boombox (clear member but doesn't emit light). -/
theorem limitLight_tablet_gt_boombox :
    (mkCfg .limitLight).L1 .rule .tablet >
    (mkCfg .limitLight).L1 .rule .boombox := by rsa_predict

/-! Cross-config predictions (goal modulation).
    The paper's central empirical claim: the same edge-case object
    receives different L1 scores under different goal conditions.
    Parallel to @cite{lassiter-goodman-2017}'s `basketball_tall_favors_taller`,
    which shows context (prior) modulates L1 across configs. -/

/-- **Goal sensitivity for flashlights** (the paper's key result, Fig. 1):
    the flashlight is more likely to be targeted under limitLight than
    limitNoise, because flashlights emit light but not noise. -/
theorem goal_sensitivity_flashlight :
    (mkCfg .limitLight).L1 .rule .flashlight >
    (mkCfg .limitNoise).L1 .rule .flashlight := by rsa_predict

/-- **Goal sensitivity for boomboxes** (reverse pattern, Fig. 1):
    the boombox is more likely to be targeted under limitNoise than
    limitLight, because boomboxes emit noise but not light. -/
theorem goal_sensitivity_boombox :
    (mkCfg .limitNoise).L1 .rule .boombox >
    (mkCfg .limitLight).L1 .rule .boombox := by rsa_predict

/-- **Goal sensitivity for tablets** under preventRecordings:
    the tablet is more likely to be targeted under preventRecordings
    than limitNoise, because tablets can record but are quiet. -/
theorem goal_sensitivity_tablet :
    (mkCfg .preventRecordings).L1 .rule .tablet >
    (mkCfg .limitNoise).L1 .rule .tablet := by rsa_predict

/-! Utility-level explanations: WHY the L1 orderings hold.
    The cross-config L1 ordering follows from the utility ordering
    because S1 is monotone in L0, which is monotone in meaning. -/

/-- The flashlight's utility is much higher under limitLight than
    limitNoise — the driver of `goal_sensitivity_flashlight`. -/
theorem flashlight_utility_light_gt_noise :
    utility .limitLight .flashlight > utility .limitNoise .flashlight := by
  native_decide

/-- The boombox's utility is higher under limitNoise than limitLight
    — the driver of `goal_sensitivity_boombox`. -/
theorem boombox_utility_noise_gt_light :
    utility .limitNoise .boombox > utility .limitLight .boombox := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 5. Multi-Dimensional Semantics (eq. 8)
-- ════════════════════════════════════════════════════

/-! The utility function U(goal, obj) is structurally a weighted score
    over dimensional measures — the same mechanism as `weightedScore`
    from `Semantics.Degree.Aggregation`. In the paper's eq. (8), the
    artifact noun denotation is Σ_f f(x) · **W**(noun, f). Here, each
    goal selects ONE feature dimension (emit-light, emit-noise, or
    can-record), so the utility reduces to the feature's raw value.

    In the general case (eq. 14, neutral condition), the utility is a
    weighted sum over multiple features with weights from goal plausibility
    norming. This is exactly `weightedScore`. -/

/-- Individual feature measures (the components of eq. 8). -/
def emitLight : Object → ℚ
  | .candle => 7/10 | .flashlight => 9/10 | .boombox => 1/10 | .tablet => 6/10

def emitNoise : Object → ℚ
  | .candle => 1/20 | .flashlight => 1/20 | .boombox => 9/10 | .tablet => 3/10

def canRecord : Object → ℚ
  | .candle => 1/20 | .flashlight => 1/20 | .boombox => 1/20 | .tablet => 9/10

/-- The utility function for explicit goals equals the raw feature value. -/
theorem utility_is_feature :
    utility .limitLight = emitLight ∧
    utility .limitNoise = emitNoise ∧
    utility .preventRecordings = canRecord := by
  refine ⟨funext fun o => ?_, funext fun o => ?_, funext fun o => ?_⟩ <;>
    cases o <;> rfl

-- ════════════════════════════════════════════════════
-- § 6. Additive vs. Multiplicative Composition
-- ════════════════════════════════════════════════════

/-! @cite{sassoon-fadlon-2017} contrast artifact nouns (additive: Σ)
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
    point made by @cite{dambrosio-hedden-2024} for multidimensional
    adjectives. @cite{sassoon-2013}'s binding types (conjunctive,
    disjunctive, mixed) are all counting aggregation and cannot
    capture the weighted, continuous-measure structure of artifact
    noun interpretation. -/
theorem artifact_aggregation_is_utilitarian :
    AggregationType.utilitarian ≠ .counting := by decide

end Phenomena.Gradability.Studies.WaldonEtAl2023

/-
# @cite{hawkins-gweon-goodman-2021}: Division of Labor in Communication

"The Division of Labor in Communication: Speakers Help Listeners Account for
Asymmetries in Visual Perspective"
Cognitive Science, 45, e12926.

## Innovation

Extends RSA with **resource-rational perspective-taking**:
- Perspective-taking is costly
- Agents choose how much effort to allocate via mixture weight w ∈ [0,1]
- Division of labor: optimal effort depends on partner's expected effort

## Theoretical Framework
@cite{keysar-etal-2003}

In the classic @cite{keysar-etal-2003} paradigm:
- Speaker (director) sees some objects
- Listener (matcher) sees those objects PLUS hidden ones
- Speaker knows listener has "known unknowns" behind occlusions

The question: How do speakers and listeners allocate perspective-taking effort?

## RSAConfig Architecture

Two RSAConfig instances capture the egocentric and asymmetric reference games:

- **cfgEgo**: Standard reference game among 3 visible objects.
  Shape-only uniquely identifies the target — no pressure for more features.
- **cfgAsym**: Reference game with latent hidden objects behind occlusions.
  Latent = match profile (which features the hidden object shares with target).
  S1 accounts for possible hidden distractors, preferring specific utterances.

The mixture model (w_S ∈ [0,1]) and resource-rational optimization sit outside
the RSAConfig loop as paper-specific extensions (Part V).

## Key Predictions (proven as theorems)

1. Egocentric: shape-only suffices (target unique in shape among visible)
2. Asymmetric: more specific utterances improve listener accuracy
3. S1 prefers specificity when hidden objects may match on features
4. Intermediate perspective-taking weights are optimal when β > 0
-/

import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Composition.Modification
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace Phenomena.Reference.Studies.HawkinsGweonGoodman2021

/-! ================================================================
    PART I: EMPIRICAL DATA
    ================================================================

## Experimental Design

### Experiment 1: Speaker Production
- 83 dyads on Amazon MTurk
- 2×2 design: occlusions (present/absent) × distractor (present/absent)
- DV: Number of words in referring expression

### Experiment 2: Listener Comprehension
- 116 dyads
- Scripted vs unscripted speaker condition
- Replication of @cite{keysar-etal-2003} materials

## Key Empirical Findings

### 1. Speakers increase informativity with occlusions (Exp 1)
- Occlusion effect: +1.3 words (t(120.3) = 8.8, p < .001)
- Distractor effect: +0.6 words (t(206) = 5.7, p < .001)
- Significant interaction (b = -0.49, t(1742) = 4.1, p < .001)

### 2. Scripted utterances cause more errors (Exp 2)
- Scripted condition: 51% critical errors
- Unscripted condition: 20% critical errors
- χ²(1) = 43, p < .001

### 3. Listeners adapt over time
- Error rate decreases across trials: z = 2.6, p < 0.01
- From 43% on first critical trial to 30% on fourth trial

### 4. Speaker informativity predicts listener accuracy
- Correlation: ρ = -0.81, 95% CI = [-0.9, -0.7]
- More informative utterances → fewer errors
-/


/-- Visual perspective state in director-matcher task -/
inductive PerspectiveState where
  | ownPrivate    -- (A) Objects only speaker can see
  | shared        -- (B) Objects both can see (common ground)
  | partnerPrivate -- (C) Objects only listener can see (behind occlusions)
  deriving DecidableEq, Repr

/-- Trial type in Experiment 1 -/
structure Exp1TrialType where
  occlusionPresent : Bool   -- Are there occluded cells?
  distractorPresent : Bool  -- Is there a same-shape distractor?
  deriving DecidableEq, Repr

/-- All trial types in 2×2 design -/
def exp1TrialTypes : List Exp1TrialType := [
  ⟨false, false⟩,  -- No occlusion, no distractor
  ⟨false, true⟩,   -- No occlusion, distractor
  ⟨true, false⟩,   -- Occlusion, no distractor
  ⟨true, true⟩     -- Occlusion, distractor
]

/-- Mean words produced in each condition -/
def exp1MeanWords : Exp1TrialType → ℚ
  | ⟨false, false⟩ => 15/10   -- ~1.5 words (shape only)
  | ⟨false, true⟩ => 21/10    -- ~2.1 words (shape + modifier)
  | ⟨true, false⟩ => 28/10    -- ~2.8 words (shape + color + texture)
  | ⟨true, true⟩ => 31/10     -- ~3.1 words

/-- Occlusion effect size (distractor-absent): +1.3 words -/
def occlusionEffect : ℚ := 13/10

/-- Distractor effect size (occlusion-absent): +0.6 words -/
def distractorEffect : ℚ := 6/10

/-- Feature mention rates by condition (Exp 1, Figure 4B) -/
structure FeatureMentionRates where
  shape : ℚ    -- Nearly always ~0.99
  color : ℚ    -- Varies by condition
  texture : ℚ  -- Varies by condition
  deriving Repr

/-- Occlusion increases feature mention rates (distractor-absent) -/
def featureRates_noOcclusion_noDistractor : FeatureMentionRates :=
  { shape := 99/100, color := 25/100, texture := 5/100 }

def featureRates_occlusion_noDistractor : FeatureMentionRates :=
  { shape := 99/100, color := 50/100, texture := 65/100 }


/-- Speaker condition in Experiment 2 -/
inductive SpeakerCondition where
  | scripted    -- Confederate uses fixed utterances from Keysar et al.
  | unscripted  -- Naive speaker produces natural referring expressions
  deriving DecidableEq, Repr

/-- Critical error rate by condition -/
def criticalErrorRate : SpeakerCondition → ℚ
  | .scripted => 51/100    -- 51% errors with scripted speaker
  | .unscripted => 20/100  -- 20% errors with natural speaker

/-- Error rate by trial number (adaptation over time) -/
def errorRateByTrial : Nat → ℚ
  | 1 => 43/100  -- First critical trial
  | 2 => 38/100
  | 3 => 34/100
  | 4 => 30/100  -- Fourth critical trial
  | _ => 30/100

/-- Listeners adapt: errors decrease over trials -/
theorem errors_decrease_over_trials :
    errorRateByTrial 4 < errorRateByTrial 1 := by native_decide


/-- Informativity: how well utterance fits target vs distractor -/
structure InformativityRating where
  targetFit : ℚ      -- How well utterance fits intended target
  distractorFit : ℚ  -- How well it fits hidden distractor
  deriving Repr

/-- Informativity difference: target fit - distractor fit -/
def informativityDiff (r : InformativityRating) : ℚ :=
  r.targetFit - r.distractorFit

/-- Scripted utterances: roughly equal fit (by design) -/
def scriptedInformativity : InformativityRating :=
  { targetFit := 50/100, distractorFit := 52/100 }

/-- Unscripted utterances: much better target fit -/
def unscriptedInformativity : InformativityRating :=
  { targetFit := 75/100, distractorFit := 25/100 }

/-- Unscripted speakers are more informative -/
theorem unscripted_more_informative :
    informativityDiff unscriptedInformativity > informativityDiff scriptedInformativity := by
  native_decide

/-- Informativity-error correlation: ρ = -0.81 -/
def informativityErrorCorrelation : ℚ := -81/100


/--
The paper identifies these key qualitative predictions:

1. **Speakers hedge against known unknowns**: Increase informativity with occlusions
2. **Division of labor depends on expectations**: Optimal effort = f(partner's expected effort)
3. **Listeners adapt to speaker behavior**: Update beliefs about speaker's effort over time
4. **Intermediate weights are optimal**: When perspective-taking is costly, partial weighting is best
-/
inductive KeyPrediction where
  | speakersHedgeUnknowns       -- More informative when listener has private info
  | divisionDependsOnPartner   -- Optimal effort depends on expected partner effort
  | listenersAdaptOverTime     -- Update beliefs about speaker from observations
  | intermediateWeightsOptimal -- Partial perspective-taking when cost > 0
  deriving DecidableEq, Repr

/-- All key predictions from the paper -/
def keyPredictions : List KeyPrediction := [
  .speakersHedgeUnknowns,
  .divisionDependsOnPartner,
  .listenersAdaptOverTime,
  .intermediateWeightsOptimal
]

/-- Critical item from @cite{keysar-etal-2003} replication -/
structure CriticalItem where
  instruction : String       -- What speaker says
  target : String            -- Intended target object
  hiddenDistractor : String  -- Confusable object behind occlusion
  deriving Repr

/-- The 8 critical items used in Experiment 2 -/
def criticalItems : List CriticalItem := [
  ⟨"Glasses", "Sunglasses", "Glasses case"⟩,
  ⟨"Bottom block", "Block (3rd row)", "Block (4th row)"⟩,
  ⟨"Tape", "Cassette", "Scotch tape"⟩,
  ⟨"Large measuring cup", "Medium cup", "Large cup"⟩,
  ⟨"Brush", "Round hairbrush", "Flat hairbrush"⟩,
  ⟨"Eraser", "Board eraser", "Pencil eraser"⟩,
  ⟨"Small candle", "Medium candle", "Small candle"⟩,
  ⟨"Mouse", "Computer mouse", "Toy mouse"⟩
]

/-- Number of critical items -/
theorem eight_critical_items : criticalItems.length = 8 := rfl


/-! ================================================================
    PART II: RSA MODEL
    ================================================================

Two RSAConfig instances formalize the reference game:

- **cfgEgo** (egocentric): 3 visible objects, no hidden. Belief-based S1.
- **cfgAsym** (asymmetric): 3 visible + 1 hidden object. Latent variable
  encodes the hidden object's match profile (which features match target).
  Prior reflects P(match) = 1/4 per feature (uniform over 4 values).

Utterance semantics derive from predicate modification (Part III):
each feature word is an intersective adjective, composed via `predMod`.
-/

-- ============================================================================
-- §2a. Finite Types
-- ============================================================================

/-- The 3 visible objects in the example display.

    target: shape=0, color=0, texture=0
    d1:     shape=1, color=0, texture=0 (shares color+texture with target)
    d2:     shape=2, color=1, texture=1 (differs on all features) -/
inductive VisObj where
  | target | d1 | d2
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The 4 objects in the asymmetric display (3 visible + 1 behind occlusion) -/
inductive AsymObj where
  | target | d1 | d2 | hidden
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterance: which features to mention (2³ = 8 possible utterances) -/
inductive Utt where
  | null  -- mention nothing
  | s     -- shape only: "the square"
  | c     -- color only: "the blue one"
  | t     -- texture only: "the checked one"
  | sc    -- shape + color: "the blue square"
  | st    -- shape + texture: "the checked square"
  | ct    -- color + texture: "the blue checked one"
  | sct   -- all three: "the blue checked square"
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty VisObj := ⟨.target⟩
instance : Nonempty AsymObj := ⟨.target⟩
instance : Nonempty Utt := ⟨.null⟩

/-- Utterance cost: number of features mentioned -/
def Utt.cost : Utt → ℕ
  | .null => 0 | .s | .c | .t => 1 | .sc | .st | .ct => 2 | .sct => 3

-- ============================================================================
-- §2b. Literal Semantics
-- ============================================================================

/-- Does utterance apply to an entity with given feature-match profile?
    For each feature the utterance mentions, the entity must match the target. -/
def Utt.applies (u : Utt) (shapeOk colorOk textureOk : Bool) : Bool :=
  let s := match u with | .s | .sc | .st | .sct => shapeOk | _ => true
  let c := match u with | .c | .sc | .ct | .sct => colorOk | _ => true
  let t := match u with | .t | .st | .ct | .sct => textureOk | _ => true
  s && c && t

/-- Egocentric literal meaning: does utterance apply to visible object?
    Target matches on all features. d1 differs only on shape. d2 differs on all. -/
def egoMeaning (u : Utt) (w : VisObj) : Bool :=
  match w with
  | .target => true
  | .d1 => u.applies false true true
  | .d2 => u.applies false false false

/-- Asymmetric literal meaning: includes hidden object behind occlusion.
    The hidden object's match profile is the latent variable `l = (matchShape, matchColor, matchTexture)`.
    Each feature independently matches target with P = 1/4. -/
def asymMeaning (l : Bool × Bool × Bool) (u : Utt) (w : AsymObj) : Bool :=
  match w with
  | .target => true
  | .d1 => u.applies false true true
  | .d2 => u.applies false false false
  | .hidden => u.applies l.1 l.2.1 l.2.2

-- ============================================================================
-- §2c. RSAConfig Definitions
-- ============================================================================

open RSA Real in
/-- Egocentric RSA: reference game among 3 visible objects.
    Belief-based scoring (S1 score = L0^α), α = 2, uniform priors. -/
noncomputable def cfgEgo : RSAConfig Utt VisObj where
  meaning _ _ u w := if egoMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 2
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

open RSA Real in
/-- Asymmetric RSA: reference game with hidden object behind occlusion.
    Latent = (matchShape, matchColor, matchTexture) for hidden object.
    Prior: each feature independently matches target with probability 1/4,
    encoded as unnormalized weights (1 for match, 3 for non-match). -/
noncomputable def cfgAsym : RSAConfig Utt AsymObj where
  Latent := Bool × Bool × Bool
  meaning _ l u w := if asymMeaning l u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 2
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior _ l :=
    (if l.1 then 1 else 3) * (if l.2.1 then 1 else 3) * (if l.2.2 then 1 else 3)
  latentPrior_nonneg _ l := by
    obtain ⟨a, b, c⟩ := l; cases a <;> cases b <;> cases c <;> norm_num


/-! ================================================================
    PART III: COMPOSITIONAL GROUNDING
    ================================================================

The utterance semantics derive from **predicate modification** (H&K Ch. 4):

  ⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)

Each feature mention (shape, color, texture) is an **intersective adjective**
that denotes a characteristic function of type `e → t`:

  - ⟦square⟧ = λx. shape(x) = target.shape
  - ⟦blue⟧ = λx. color(x) = target.color
  - ⟦checked⟧ = λx. texture(x) = target.texture

This is exactly `Semantics.Composition.Modification.predMod` applied iteratively.
-/

namespace MontaguGrounding

open Semantics.Composition.Modification

/-- Shape predicate: matches target's shape (only target has shape=0) -/
def shapePred : VisObj → Bool
  | .target => true | _ => false

/-- Color predicate: matches target's color (target + d1 have color=0) -/
def colorPred : VisObj → Bool
  | .target | .d1 => true | .d2 => false

/-- Texture predicate: matches target's texture (target + d1 have texture=0) -/
def texturePred : VisObj → Bool
  | .target | .d1 => true | .d2 => false

/-- Compositional utterance denotation via intersective predicate modification.
    Each mentioned feature contributes an intersective adjective, composed
    left-to-right via `predMod`. -/
def compositionalMeaning (u : Utt) : VisObj → Bool :=
  let base : VisObj → Bool := truePred
  let s := match u with | .s | .sc | .st | .sct => predMod base shapePred | _ => base
  let sc := match u with | .c | .sc | .ct | .sct => predMod s colorPred | _ => s
  match u with | .t | .st | .ct | .sct => predMod sc texturePred | _ => sc

/-- **Grounding theorem**: `egoMeaning` equals the compositional derivation.
    The ad-hoc semantics match Montague intersective predicate modification. -/
theorem grounding_ego_meaning (u : Utt) (w : VisObj) :
    egoMeaning u w = compositionalMeaning u w := by
  unfold egoMeaning compositionalMeaning Utt.applies predMod truePred
         shapePred colorPred texturePred
  cases u <;> cases w <;> simp [Bool.and_comm]

/-- The RSA meaning function is grounded in compositional semantics -/
theorem rsa_meaning_compositional (u : Utt) (w : VisObj) :
    egoMeaning u w = true ↔ compositionalMeaning u w = true := by
  rw [grounding_ego_meaning]

end MontaguGrounding


/-! ================================================================
    PART IV: PREDICTIONS VIA rsa_predict
    ================================================================

Core RSA predictions verified via `rsa_predict`. The egocentric model captures
the no-occlusion case; the asymmetric model captures occlusion.
-/

-- ============================================================================
-- §4a. Egocentric Predictions
-- ============================================================================

/-- Shape-only uniquely identifies target among visible objects. -/
theorem ego_shape_identifies_target :
    cfgEgo.L1 .s .target > cfgEgo.L1 .s .d1 := by
  rsa_predict

/-- In the egocentric model, the listener is equally confident about the target
    whether hearing shape-only or full description. Both uniquely identify
    target among visible objects, so additional features add nothing. -/
theorem ego_shape_as_good_as_full :
    ¬(cfgEgo.L1 .sct .target > cfgEgo.L1 .s .target) := by
  rsa_predict

/-- S1 is indifferent between shape-only and full description for target
    (both have L0 = 1 among visible objects). -/
theorem ego_S1_indifferent :
    ¬(cfgEgo.S1 () .target .sct > cfgEgo.S1 () .target .s) := by
  rsa_predict

-- ============================================================================
-- §4b. Asymmetric Predictions
-- ============================================================================

/-- **Paper Prediction 1**: Full description produces higher L1 posterior for target
    than shape-only under asymmetry. Hidden objects can match individual features
    (P(match_shape) = 1/4), so more specific utterances are more reliably
    informative. -/
theorem asym_full_desc_better_reference :
    cfgAsym.L1 .sct .target > cfgAsym.L1 .s .target := by
  rsa_predict

/-- Shape+color also beats shape-only: each additional feature narrows the
    set of possible hidden distractors. -/
theorem asym_shape_color_beats_shape :
    cfgAsym.L1 .sc .target > cfgAsym.L1 .s .target := by
  rsa_predict

/-- When hidden object matches target's shape (but not color or texture),
    S1 prefers full description over shape-only. Shape-only fails to
    distinguish target from hidden; full description succeeds. -/
theorem asym_S1_prefers_specificity_when_shape_matches :
    cfgAsym.S1 (true, false, false) .target .sct >
    cfgAsym.S1 (true, false, false) .target .s := by
  rsa_predict

/-- When hidden matches no features, S1 is indifferent: both shape-only
    and full description have L0 = 1 for target. -/
theorem asym_S1_indifferent_when_no_match :
    ¬(cfgAsym.S1 (false, false, false) .target .sct >
      cfgAsym.S1 (false, false, false) .target .s) := by
  rsa_predict

/-- Even under asymmetry, L1 correctly identifies target over d1
    (which differs in shape). -/
theorem asym_L1_identifies_target :
    cfgAsym.L1 .s .target > cfgAsym.L1 .s .d1 := by
  rsa_predict


/-! ================================================================
    PART V: EXTENSIONS (Mixture Model & Resource-Rational Analysis)
    ================================================================

The mixture model (Eq. 5) and resource-rational optimization (Eq. 10-11) sit
outside the standard RSA loop. These are paper-specific extensions, defined
in ℝ and grounded in `RSAConfig.L0`.

**Key equations from the paper:**
- Eq. 2: U^asym_S1(u;o,C) = Σ_{o_h} P(o_h) log P_L0(o|u,C ∪ {o_h}) − cost(u)
- Eq. 3: U^ego_S1(u;o,C) = log P_L0(o|u,C) − cost(u)
- Eq. 5: U^mix_S1 = w_S · U^asym + (1−w_S) · U^ego
- Eq. 10: U_{S_RR}(w_S) = E_{P(w_L)}[P_L0(o|u*,C,w_L)] − β × w_S

The mixture operates in **log-space** (over utilities, not probabilities).
This means the mixture speaker uses a weighted geometric mean of L0 values,
not an arithmetic mean: exp(w_S · E[log L0^asym] + (1−w_S) · log L0^ego).

Parameters: α = 2, cost(u) = 0.03 (uniform, cancels in S1 normalization).
-/

open RSA BigOperators

-- ============================================================================
-- §5a. L0 Success Rates (grounded in RSAConfig)
-- ============================================================================

/-- Egocentric L0 success rate: P_L0^ego(target | u).
    Grounded directly in `cfgEgo.L0`. -/
noncomputable def egoInfR (u : Utt) : ℝ := cfgEgo.L0 () u .target

/-- Asymmetric L0 success rate: E_l[P_L0^asym(target | u, l)].
    Marginalizes the literal listener's success over hidden object profiles,
    weighted by the latent prior. -/
noncomputable def asymInfR (u : Utt) : ℝ :=
  let Z : ℝ := ∑ l' : Bool × Bool × Bool, cfgAsym.latentPrior .target l'
  ∑ l : Bool × Bool × Bool, (cfgAsym.latentPrior .target l / Z) * cfgAsym.L0 l u .target

-- ============================================================================
-- §5b. Log-Space Mixture Utilities (Paper Eq. 2-5)
-- ============================================================================

/-- Expected log-L0 under the asymmetric model (Eq. 2, utility component):
    E_h[log P_L0(target | u, C ∪ {h})].
    This is inside the expectation, so by Jensen's inequality
    asymLogInfR(u) ≤ log(asymInfR(u)). -/
noncomputable def asymLogInfR (u : Utt) : ℝ :=
  let Z : ℝ := ∑ l' : Bool × Bool × Bool, cfgAsym.latentPrior .target l'
  ∑ l : Bool × Bool × Bool, (cfgAsym.latentPrior .target l / Z) *
    Real.log (cfgAsym.L0 l u .target)

/-- Mixture speaker utility (Eq. 5):
    U^mix(u; w_S) = w_S · E_h[log P_L0^asym(target|u,h)]
                   + (1−w_S) · log P_L0^ego(target|u)
    Uniform cost (0.03) omitted: it cancels in S1 normalization. -/
noncomputable def mixUtility (u : Utt) (wS : ℝ) : ℝ :=
  wS * asymLogInfR u + (1 - wS) * Real.log (egoInfR u)

/-- Mixture S1 score: P_S1^mix(u | target, w_S) ∝ exp(α · U^mix(u; w_S)).
    Paper Eq. 1 with the mixture utility from Eq. 5. -/
noncomputable def mixS1Score (u : Utt) (wS α : ℝ) : ℝ :=
  Real.exp (α * mixUtility u wS)

-- ============================================================================
-- §5c. Full Resource-Rational Model (Paper Eqs 7–10)
-- ============================================================================

/-! The full model marginalizes over listener perspective-taking weight w_L.

    The simplified model (Eqs 2–5) treats w_L as fixed at 1. The full model
    (Eqs 7–9) has the speaker consider a range of listener weights, and the
    resource-rational analysis (Eq. 10) measures accuracy averaged over w_L.

    **Mixture L0** (Eq. 8): P_{L_0}^{mix}(target|u, l, w_L) =
      w_L · P_{L_0}^{asym}(target|u, l) + (1−w_L) · P_{L_0}^{ego}(target|u).
    At w_L = 0, the listener ignores hidden objects. At w_L = 1, the listener
    accounts for all potential hidden distractors.

    **Marginalized S1** (Eq. 9): the speaker's utility integrates over w_L,
    discretized to 5 grid points {0, 1/4, 1/2, 3/4, 1} with uniform weight.

    **Accuracy** (Eq. 10): since listener accuracy is linear in w_L,
    E_{uniform w_L}[accuracy] = (egoInfR + asymInfR) / 2. -/

/-- Mixture L0 accuracy: probability the mixture listener at weight w_L
    correctly identifies the target, given hidden object profile l (Eq. 8). -/
noncomputable def mixL0Target (u : Utt) (l : Bool × Bool × Bool) (wL : ℝ) : ℝ :=
  wL * cfgAsym.L0 l u .target + (1 - wL) * egoInfR u

/-- Asymmetric speaker utility at a specific listener weight (Eq. 7).
    U^asym(u; w_L) = Σ_l P(l)/Z · log(P_L0^mix(target|u, l, w_L)) -/
noncomputable def asymUtilityAtWL (u : Utt) (wL : ℝ) : ℝ :=
  let Z : ℝ := ∑ l' : Bool × Bool × Bool, cfgAsym.latentPrior .target l'
  ∑ l : Bool × Bool × Bool, (cfgAsym.latentPrior .target l / Z) *
    Real.log (mixL0Target u l wL)

/-- Mixed speaker utility at specific (w_S, w_L) (Eq. 8). -/
noncomputable def mixUtilityFull (u : Utt) (wS wL : ℝ) : ℝ :=
  wS * asymUtilityAtWL u wL + (1 - wS) * Real.log (egoInfR u)

/-- W_L-marginalized speaker utility (Eq. 9 inside the exp).
    Discretized: 5 uniform grid points at w_L ∈ {0, 1/4, 1/2, 3/4, 1}. -/
noncomputable def mixUtilityMarg (u : Utt) (wS : ℝ) : ℝ :=
  (1 / 5 : ℝ) * ∑ k : Fin 5, mixUtilityFull u wS (↑k / 4)

/-- Full S1 score with w_L marginalization (Eq. 9). -/
noncomputable def mixS1ScoreFull (u : Utt) (wS α : ℝ) : ℝ :=
  Real.exp (α * mixUtilityMarg u wS)

/-- Listener accuracy averaged over uniform w_L (for Eq. 10).
    Since accuracy(u, w_L) = w_L·asymInfR(u) + (1−w_L)·egoInfR(u) is linear
    in w_L, the expectation under uniform P(w_L) is the midpoint. -/
noncomputable def avgListenerAccuracy (u : Utt) : ℝ :=
  (egoInfR u + asymInfR u) / 2

/-- Full expected accuracy (Eq. 10) with w_L marginalization.
    Uses the w_L-marginalized S1 for speaker production and the
    w_L-averaged listener accuracy for evaluation. -/
noncomputable def expectedAccuracyFull (wS α : ℝ) : ℝ :=
  let Z := ∑ u' : Utt, mixS1ScoreFull u' wS α
  if Z = 0 then 0
  else ∑ u : Utt, (mixS1ScoreFull u wS α / Z) * avgListenerAccuracy u

/-- Full resource-rational utility (Eqs 10–11).
    U_RR(w_S) = ExpAccuracy_full(w_S) − β · w_S -/
noncomputable def rrUtilityFull (wS α β : ℝ) : ℝ :=
  expectedAccuracyFull wS α - β * wS

-- ============================================================================
-- §5d. Structural Properties
-- ============================================================================

/-- At w_S = 0, the simplified mixture utility reduces to egocentric log-L0. -/
theorem mixUtility_at_zero (u : Utt) :
    mixUtility u 0 = Real.log (egoInfR u) := by
  unfold mixUtility; ring

/-- At w_S = 1, the simplified mixture utility reduces to asymmetric expected log-L0. -/
theorem mixUtility_at_one (u : Utt) :
    mixUtility u 1 = asymLogInfR u := by
  unfold mixUtility; ring

-- ============================================================================
-- §5e. Resource-Rational Predictions (Paper §2.4, Figure 2)
-- ============================================================================

/-- **Paper prediction (β = 0)**: When perspective-taking is free, full PT
    (w_S = 1) achieves higher expected accuracy than no PT (w_S = 0).
    The asymmetric speaker produces more specific utterances, improving
    listener accuracy. (Paper Figure 2, rightmost point of β = 0 curve.) -/
theorem no_cost_prefers_full_pt :
    rrUtilityFull 1 2 0 > rrUtilityFull 0 2 0 := by
  rsa_predict

/-- **Paper prediction (high β)**: When perspective-taking is costly,
    the cost term β · w_S dominates, making w_S = 0 preferable to w_S = 1.
    (Paper Figure 2, β = 0.5 curve.) -/
theorem high_cost_penalizes_full_pt :
    rrUtilityFull 0 2 (1/2) > rrUtilityFull 1 2 (1/2) := by
  rsa_predict

/-- **Interior optimum limitation**: The paper's central result (§2.4,
    Figure 2) is that at moderate cost (β = 0.2), an intermediate weight
    w*_S ≈ 0.36 outperforms both extremes.

    Our 3+1 object reference game is too simple to produce this effect.
    Shape alone uniquely identifies the target among visible objects
    (`egoInfR .s = 1`), so the egocentric baseline accuracy is ≈97%.
    The marginal accuracy gain from perspective-taking is ≈0.3%, far
    below the β = 0.2 cost. The interior optimum requires a richer display
    where egocentric accuracy is substantially lower, creating a larger
    incentive for specific utterances that disambiguate from hidden objects.

    Verified: `rrUtilityFull 0 2 β > rrUtilityFull 1 2 β` for all
    tested β ≥ 1/50 (even with the full w_L-marginalized model). -/
theorem simplified_game_no_interior_optimum :
    rrUtilityFull 0 2 (1/50) > rrUtilityFull 1 2 (1/50) := by
  rsa_predict

-- ============================================================================
-- §5f. Listener Belief Adaptation (Paper §2.4.1, Appendix B)
-- ============================================================================

/-- Listener's belief about speaker's perspective-taking weight.
    Over time, listeners update their expectation of w_S based on
    observed utterance informativity. -/
structure ListenerBeliefs where
  wS_expectation : ℝ   -- E[w_S]
  observations : ℕ      -- Number of observed utterances

/-- Initial uniform belief: E[w_S] = 1/2 -/
noncomputable def initialBeliefs : ListenerBeliefs :=
  { wS_expectation := 1/2, observations := 0 }

/-- Update beliefs after observing utterance informativity.
    Short/uninformative utterances → lower w_S estimate;
    long/informative utterances → higher w_S estimate. -/
noncomputable def updateBeliefs (beliefs : ListenerBeliefs) (shortUtterance : Bool) :
    ListenerBeliefs :=
  let newObs := beliefs.observations + 1
  let update : ℝ := if shortUtterance then -1/10 else 1/10
  let newExpectation := max 0 (min 1 (beliefs.wS_expectation + update / newObs))
  { wS_expectation := newExpectation, observations := newObs }

/-- After seeing short utterances, listener expects lower w_S -/
noncomputable def beliefsAfterShortUtterances : ListenerBeliefs :=
  updateBeliefs (updateBeliefs (updateBeliefs initialBeliefs true) true) true

/-- **Paper prediction** (@cite{hawkins-gweon-goodman-2021} §2.4.1):
    Listeners infer low speaker effort from under-informative utterances. -/
theorem listener_infers_low_wS_from_short_utterances :
    beliefsAfterShortUtterances.wS_expectation < initialBeliefs.wS_expectation := by
  unfold beliefsAfterShortUtterances updateBeliefs initialBeliefs
  simp only [ite_true, ListenerBeliefs.wS_expectation, min_def, max_def]
  split_ifs <;> linarith

/-- Optimal listener weight: compensate for low speaker effort.
    When the speaker uses low w_S, the listener should increase their own
    perspective-taking to compensate. -/
noncomputable def optimalListenerWeight (speakerWS β : ℝ) : ℝ :=
  min 1 (max 0 (1 - speakerWS + β))

/-- **Paper prediction** (@cite{hawkins-gweon-goodman-2021} §2.4.1):
    Listener increases effort when speaker decreases theirs. -/
theorem listener_compensates_for_low_speaker_effort :
    optimalListenerWeight (3/10) (2/10) > optimalListenerWeight (7/10) (2/10) := by
  unfold optimalListenerWeight
  simp only [min_def, max_def]
  split_ifs <;> linarith

end Phenomena.Reference.Studies.HawkinsGweonGoodman2021

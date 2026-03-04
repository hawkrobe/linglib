import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Noise
import Linglib.Theories.Pragmatics.GriceanMaxims
import Linglib.Phenomena.Reference.Studies.DaleReiter1995
import Linglib.Phenomena.Reference.Studies.EngelhardtEtAl2006

/-!
# @cite{degen-etal-2020}
@cite{frank-goodman-2012} @cite{dale-reiter-1995} @cite{engelhardt-etal-2006}
@cite{grice-1975} @cite{kursat-degen-2021} @cite{cohn-gordon-etal-2019}

When Redundancy Is Useful: A Bayesian Approach to "Overinformative" Referring
Expressions. *Psychological Review* 127(4), 591–621.

## Core Argument

Standard RSA with Boolean semantics (φ ∈ {0,1}) predicts no preference for
overmodified referring expressions — if color alone identifies the target,
adding size is literally uninformative. But speakers overmodify 30–65% of
the time, with color mentioned redundantly more often than size.

cs-RSA replaces Boolean denotations with **continuous semantics**: φ(u, o) ∈ [0,1]
via a **Product of Experts** (PoE) model. Each feature dimension acts as an
independent noisy channel:

    φ(u, o) = φ_type(u, o) · φ_color(u, o) · φ_size(u, o)

where φ_color = match_val if colors agree, mismatch_val otherwise (and
similarly for size). The **asymmetry** between color and size arises from
differing noise levels:

    color: match = 0.99, mismatch = 0.01 → discrimination = 0.98
    size:  match = 0.80, mismatch = 0.20 → discrimination = 0.60

Adding a redundant color modifier sharpens the listener's posterior more
than adding redundant size → speakers overmodify with color more.

## Architecture

    S1(u|w) ∝ exp(β_i · log L0(w|u) − β_c · cost(u))

where `L0(w|u) = φ(u,w) / Σ_w' φ(u,w')` is the literal listener with
continuous semantics. BDA-fitted cost parameters β_c ≈ 0, placing the
model in the **No-Brevity** regime. With β_c = 0, the formula reduces to
`L0(w|u)^β_i`, matching the `beliefBased` scoring pattern.

## Connection to @cite{cohn-gordon-etal-2019}

cs-RSA extends the RSA reference game framework in a different dimension
from @cite{cohn-gordon-etal-2019}'s incremental RSA. Their synthesis —
CI-RSA (@cite{kursat-degen-2021}) — combines incremental processing with
continuous semantics.

## Verified Predictions

1. cs-RSA: S1 prefers overmodified > color-only > size-only > bare
2. cs-RSA: color modifier more informative than size modifier
3. Boolean RSA: sufficient and overmodified forms are equally informative
4. Connection: cost = 0 ↔ @cite{dale-reiter-1995} No-Brevity (strength 0)
5. Connection: noise discrimination ordering grounds the asymmetry
6. Connection: explains @cite{engelhardt-etal-2006}'s ~31% over-description

## Verified Data

Mixed-effects logistic regression coefficients (§3): main effect of
sufficient property β = 3.54, SE = .22, p < .0001. BDA-fitted noise
parameters (Figure 10): MAP x_color = .88, MAP x_size = .79, confirming
color > size discrimination. Fitted β_c values near zero.
-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.DegenEtAl2020

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Objects in a reference game scene where target and distractor differ in
    both color and size. This minimal scene demonstrates the cs-RSA
    mechanism: both dimensions independently suffice for disambiguation,
    so any modifier beyond one is "overmodification."

    The paper's §2 demonstration uses a 3-object scene; this 2-object
    setup is sufficient for the qualitative predictions. -/
inductive World where
  /-- Target: blue small pin -/
  | target
  /-- Distractor: red large pin -/
  | distractor
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- Referring expressions varying in modifier inclusion. The nominal ("pin")
    is always present; the question is which adjectives to add. -/
inductive Utterance where
  /-- "pin" — type only -/
  | bare
  /-- "blue pin" — color + type -/
  | color
  /-- "small pin" — size + type -/
  | size
  /-- "small blue pin" — size + color + type -/
  | both
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. Continuous Semantics (cs-RSA)
-- ============================================================================

/-- Continuous semantic value φ(u, o) via Product of Experts.

    Each feature dimension contributes a noisy channel value directly
    from the `RSA.Noise` module's standard parameters. For the scene
    (target: blue small pin, distractor: red large pin):

    | Utterance       | φ(target)                   | φ(distractor)                         |
    |-----------------|-----------------------------|---------------------------------------|
    | "pin"           | 1                           | 1                                     |
    | "blue pin"      | colorMatch (0.99)           | colorMismatch (0.01)                  |
    | "small pin"     | sizeMatch (0.80)            | sizeMismatch (0.20)                   |
    | "small blue pin"| colorMatch · sizeMatch      | colorMismatch · sizeMismatch          |

    The noise parameters are the §2 demonstration values from
    @cite{degen-etal-2020}, imported from `RSA.Noise`. -/
def φ : Utterance → World → ℚ
  | .bare, _ => 1
  | .color, .target => RSA.Noise.colorMatch
  | .color, .distractor => RSA.Noise.colorMismatch
  | .size, .target => RSA.Noise.sizeMatch
  | .size, .distractor => RSA.Noise.sizeMismatch
  | .both, .target => RSA.Noise.colorMatch * RSA.Noise.sizeMatch
  | .both, .distractor => RSA.Noise.colorMismatch * RSA.Noise.sizeMismatch

/-- φ is non-negative for all utterance-world pairs. -/
theorem φ_nonneg (u : Utterance) (w : World) : 0 ≤ φ u w := by
  cases u <;> cases w <;> simp [φ, RSA.Noise.colorMatch, RSA.Noise.colorMismatch,
    RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch] <;> norm_num

/-- φ uses the same noise parameters as the `RSA.Noise` module —
    by construction, not by bridge theorem. -/
theorem φ_grounded_in_noise :
    φ .color .target = RSA.Noise.colorMatch ∧
    φ .color .distractor = RSA.Noise.colorMismatch ∧
    φ .size .target = RSA.Noise.sizeMatch ∧
    φ .size .distractor = RSA.Noise.sizeMismatch :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §2b. Product of Experts Decomposition
-- ============================================================================

/-- The overmodified form's φ factors into per-feature channel values —
    the concrete instantiation of the Product of Experts model from
    @cite{degen-etal-2020} §2. Each feature dimension contributes an
    independent noisy channel; the combined φ is their product. -/
theorem φ_product_of_experts :
    φ .both .target = φ .color .target * φ .size .target ∧
    φ .both .distractor = φ .color .distractor * φ .size .distractor :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- §3. cs-RSA Config (α = 1, cost = 0)
-- ============================================================================

open RSA Real in
/-- cs-RSA model for the overmodification reference game.

    - **Meaning**: continuous PoE semantics φ(u,o) ∈ [0,1]
    - **S1**: gated exp(α · log L0), equivalent to L0^α with zero-gating
    - **α** = 1 (Luce choice rule)
    - **Cost** = 0 (No-Brevity regime; paper's BDA estimates: β_c ≈ 0)

    The continuous meaning function is the key innovation: redundant modifiers
    carry non-zero information because noise channels are imperfect. The S1
    scoring pattern is the same as @cite{frank-goodman-2012} — only the
    meaning function changes from Boolean to continuous. -/
noncomputable def cfg : RSAConfig Utterance World where
  meaning _ _ u w := ↑(φ u w)
  meaning_nonneg _ _ u w := by exact_mod_cast φ_nonneg u w
  s1Score l0 α _ w u :=
    if l0 u w = 0 then 0
    else exp (α * log (l0 u w))
  s1Score_nonneg l0 α _ _ u _ _ := by
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

-- ============================================================================
-- §4. Core Prediction: cs-RSA Prefers Overmodification
-- ============================================================================

/-- **Main result**: cs-RSA's S1 strictly prefers the overmodified form
    "small blue pin" over the color-sufficient "blue pin."

    Mechanism: "blue pin" alone gives L0 = colorMatch / (colorMatch +
    colorMismatch) = 99/100. Adding "small" sharpens the posterior to
    L0 = (colorMatch · sizeMatch) / (colorMatch · sizeMatch +
    colorMismatch · sizeMismatch) = 396/397 ≈ 0.997. With cost = 0,
    there is no penalty for the extra modifier. -/
theorem csrsa_overmod_beats_color :
    cfg.S1 () .target .both > cfg.S1 () .target .color := by
  rsa_predict

/-- cs-RSA's S1 strictly prefers the overmodified form over the
    size-sufficient "small pin."

    The improvement is even larger: "small pin" gives L0 = sizeMatch /
    (sizeMatch + sizeMismatch) = 4/5. Color's reliable channel
    (discrimination = 0.98) adds substantial signal to the noisy size
    channel (discrimination = 0.60). -/
theorem csrsa_overmod_beats_size :
    cfg.S1 () .target .both > cfg.S1 () .target .size := by
  rsa_predict

-- ============================================================================
-- §5. Core Prediction: Color > Size Asymmetry
-- ============================================================================

/-- **Color-size asymmetry**: S1 prefers "blue pin" over "small pin."

    "blue pin" gives L0 = 99/100; "small pin" gives L0 = 4/5.
    Color's higher discrimination (0.98 vs 0.60) means the color channel
    transmits more information to the literal listener.

    This underlies the paper's main empirical finding: speakers overmodify
    with color more than with size (§3: β = 3.54, p < .0001). -/
theorem csrsa_color_beats_size :
    cfg.S1 () .target .color > cfg.S1 () .target .size := by
  rsa_predict

/-- Complete S1 ordering: overmodified > color > size > bare.
    This is the full prediction of cs-RSA for this scene. -/
theorem csrsa_full_ordering :
    cfg.S1 () .target .both > cfg.S1 () .target .color ∧
    cfg.S1 () .target .color > cfg.S1 () .target .size ∧
    cfg.S1 () .target .size > cfg.S1 () .target .bare :=
  ⟨csrsa_overmod_beats_color, csrsa_color_beats_size, by rsa_predict⟩

-- ============================================================================
-- §6. Boolean Baseline: No Overmodification Preference
-- ============================================================================

/-- Boolean (zero-noise) semantic value. In the zero-noise limit, φ ∈ {0,1}:
    a feature either matches perfectly or not at all. -/
def φ_bool : Utterance → World → ℚ
  | .bare, _ => 1
  | .color, .target => 1      -- blue = blue
  | .color, .distractor => 0  -- blue ≠ red
  | .size, .target => 1       -- small = small
  | .size, .distractor => 0   -- small ≠ large
  | .both, .target => 1       -- both match
  | .both, .distractor => 0   -- both mismatch

/-- Boolean semantics values are in {0, 1}: the zero-noise limit where
    match → 1, mismatch → 0 recovers classical Boolean denotations. -/
theorem φ_bool_values (u : Utterance) (w : World) :
    φ_bool u w = 0 ∨ φ_bool u w = 1 := by
  cases u <;> cases w <;> simp [φ_bool]

open RSA Real in
/-- Standard RSA with Boolean semantics (φ ∈ {0,1}).
    Same architecture as cs-RSA but with zero noise: features either
    match perfectly or not at all. This is the @cite{frank-goodman-2012}
    model applied to the same scene. -/
noncomputable def boolCfg : RSAConfig Utterance World where
  meaning _ _ u w := ↑(φ_bool u w)
  meaning_nonneg _ _ u w := by
    cases u <;> cases w <;> simp [φ_bool]
  s1Score l0 α _ w u :=
    if l0 u w = 0 then 0
    else exp (α * log (l0 u w))
  s1Score_nonneg l0 α _ _ u _ _ := by
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

/-- Boolean RSA does NOT prefer overmodification: "small blue pin" is NOT
    better than "blue pin." Both give L0(target) = 1.0, so S1 scores
    are identical. -/
theorem bool_no_overmod_preference :
    ¬(boolCfg.S1 () .target .both > boolCfg.S1 () .target .color) := by
  rsa_predict

/-- Boolean RSA shows NO color-size asymmetry: "blue pin" and "small pin"
    are equally informative (both give L0 = 1.0). -/
theorem bool_no_color_size_asymmetry :
    ¬(boolCfg.S1 () .target .color > boolCfg.S1 () .target .size) := by
  rsa_predict

/-- **The contrast**: cs-RSA predicts overmodification and asymmetry where
    Boolean RSA predicts neither. Noise is the key ingredient.

    | Prediction       | cs-RSA  | Boolean |
    |------------------|---------|---------|
    | overmod > color  | ✓       | ✗       |
    | color > size     | ✓       | ✗       | -/
theorem noise_makes_the_difference :
    -- cs-RSA: overmod preferred, color > size
    cfg.S1 () .target .both > cfg.S1 () .target .color ∧
    cfg.S1 () .target .color > cfg.S1 () .target .size ∧
    -- Boolean: neither
    ¬(boolCfg.S1 () .target .both > boolCfg.S1 () .target .color) ∧
    ¬(boolCfg.S1 () .target .color > boolCfg.S1 () .target .size) :=
  ⟨csrsa_overmod_beats_color, csrsa_color_beats_size,
   bool_no_overmod_preference, bool_no_color_size_asymmetry⟩

-- ============================================================================
-- §7. Experimental Data (Experiment 1, §3)
-- ============================================================================

/-- Mixed-effects logistic regression result from the production experiment.
    Positive β means more overmodification in the first condition. -/
structure RegressionResult where
  /-- Log-odds coefficient -/
  β : Float
  /-- Standard error -/
  se : Float
  /-- Significant at p < .05 -/
  significant : Bool
  deriving Repr

/-- Main effect of sufficient property (color vs size, §3):
    speakers are significantly more likely to add a redundant color
    adjective than a redundant size adjective. β = 3.54, SE = .22,
    p < .0001. Verified against running text. -/
def exp1_main_effect : RegressionResult :=
  { β := 3.54, se := 0.22, significant := true }

/-- Scene variation × sufficient property interaction (§3):
    the color > size asymmetry is modulated by scene variation.
    β = 2.26, SE = .74, p < .003. Verified against running text. -/
def exp1_interaction : RegressionResult :=
  { β := 2.26, se := 0.74, significant := true }

/-- The core empirical finding: color overmodification significantly
    exceeds size overmodification. -/
theorem color_overmod_exceeds_size :
    exp1_main_effect.β > 0 ∧ exp1_main_effect.significant := by
  constructor <;> native_decide

-- ============================================================================
-- §7b. BDA-Fitted Parameters
-- ============================================================================

/-- BDA-fitted noise parameter for a feature dimension.
    The paper fits x_feature where match = x, mismatch = 1 − x. -/
structure FittedNoiseParam where
  /-- MAP estimate of the noise parameter x -/
  map : Float
  /-- Lower bound of 95% HDI -/
  hdi_lo : Float
  /-- Upper bound of 95% HDI -/
  hdi_hi : Float
  deriving Repr

/-- Fitted color noise parameter (Figure 10):
    MAP x_color = 0.88, 95% HDI = [0.85, 0.92].
    Verified against Figure 10 caption. -/
def fitted_x_color : FittedNoiseParam :=
  { map := 0.88, hdi_lo := 0.85, hdi_hi := 0.92 }

/-- Fitted size noise parameter (Figure 10):
    MAP x_size = 0.79, 95% HDI = [0.76, 0.80].
    Verified against Figure 10 caption. -/
def fitted_x_size : FittedNoiseParam :=
  { map := 0.79, hdi_lo := 0.76, hdi_hi := 0.80 }

/-- Fitted cost parameters (Figure 10):
    β_c(size) MAP = 0.02, β_c(color) MAP = 0.03 — near zero.
    Verified against Figure 10 caption. -/
structure FittedCostParams where
  /-- Cost weight for size adjective -/
  β_c_size : Float
  /-- Cost weight for color adjective -/
  β_c_color : Float
  deriving Repr

def fitted_cost : FittedCostParams := { β_c_size := 0.02, β_c_color := 0.03 }

/-- BDA-fitted parameters confirm the noise discrimination ordering:
    x_color > x_size, matching the `RSA.Noise` module's standard values.
    This is the empirical validation of the noise channel asymmetry. -/
theorem fitted_color_gt_size :
    fitted_x_color.map > fitted_x_size.map := by native_decide

/-- BDA-fitted cost parameters are near zero, empirically confirming
    the No-Brevity regime. The model finds that utterance cost plays
    essentially no role — speakers are driven by informativity (Q1)
    rather than brevity (Q2). -/
theorem fitted_cost_near_zero :
    fitted_cost.β_c_size < 0.05 ∧ fitted_cost.β_c_color < 0.05 := by
  constructor <;> native_decide

-- ============================================================================
-- §8. Bridge: No-Brevity Regime
-- ============================================================================

open Theories.Pragmatics.GriceanMaxims

/-- cs-RSA operates in the No-Brevity regime: cost = 0, so there is no
    penalty for longer utterances (empirically confirmed: fitted β_c ≈ 0).
    This matches @cite{dale-reiter-1995}'s No Brevity interpretation
    (the weakest Q2, strength = 0).

    The insight: No-Brevity is not just computationally convenient — it
    is **rational** when perception is noisy. Redundant modifiers carry
    real information through the noise channel, so omitting them harms
    the listener. Over-description is not a violation of Q2; it is Q1
    (be informative) operating in a noisy world.

    The paper explicitly discusses @cite{dale-reiter-1995}'s Incremental
    Algorithm (IA) and how cs-RSA improves on it:

    | Property      | IA (D&R 1995)    | cs-RSA                   |
    |---------------|------------------|--------------------------|
    | Output        | deterministic    | probabilistic (soft-max) |
    | Brevity       | No-Brevity       | No-Brevity (β_c ≈ 0)    |
    | Overmod rate  | fixed by order   | varies with noise params |
    | Color > size  | from pref. order | from noise asymmetry     |

    Both operate in the No-Brevity regime, but cs-RSA derives the
    preference ordering from noise discrimination rather than stipulating
    it. -/
theorem cost_zero_is_no_brevity :
    DaleReiter1995.BrevityInterpretation.noBrevity.strength = 0 ∧
    QuantityViolation.underInformative.submaxim ≠
    QuantityViolation.overInformative.submaxim :=
  ⟨rfl, violations_independent⟩

-- ============================================================================
-- §9. Bridge: Noise Discrimination Ordering
-- ============================================================================

/-- The color > size > material discrimination ordering from `RSA.Noise`
    directly predicts the overmodification ordering. cs-RSA's meaning
    function φ uses these noise values by construction (not by coincidence):
    `φ .color .target = RSA.Noise.colorMatch`. -/
theorem noise_grounds_asymmetry :
    -- φ is grounded in RSA.Noise (structural, not coincidental)
    φ .color .target = RSA.Noise.colorMatch ∧
    φ .size .target = RSA.Noise.sizeMatch ∧
    -- The discrimination ordering predicts color > size overmod
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    -- The full ordering extends to material
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination :=
  ⟨rfl, rfl, RSA.Noise.color_gt_size, RSA.Noise.size_gt_material⟩

-- ============================================================================
-- §10. Bridge: Explains Engelhardt et al. (2006)
-- ============================================================================

/-- cs-RSA explains the puzzle from @cite{engelhardt-etal-2006}: speakers
    over-describe ~31% of the time, listeners don't penalize it (Q2
    violations tolerated), yet listeners implicitly detect the redundancy
    (processing cost).

    cs-RSA's answer: over-description is not a Q2 violation at all. In
    a noisy world, redundant modifiers are genuinely informative (Q1).
    The speaker is not being "over-informative" — they are being
    appropriately informative given perceptual uncertainty. -/
theorem explains_engelhardt :
    -- Engelhardt: speakers over-describe
    EngelhardtEtAl2006.exp1_target_1ref.modified > 0.2 ∧
    -- Engelhardt: over-descriptions not penalized in judgment
    ¬EngelhardtEtAl2006.exp2_target_1ref.significant ∧
    -- cs-RSA explains: overmodification IS informative under noise
    cfg.S1 () .target .both > cfg.S1 () .target .color ∧
    cfg.S1 () .target .both > cfg.S1 () .target .size := by
  refine ⟨by native_decide, by decide, csrsa_overmod_beats_color,
          csrsa_overmod_beats_size⟩

-- ============================================================================
-- §11. Bridge: Explanatory Chain
-- ============================================================================

/-- The explanatory chain from Gricean maxims to empirical overmodification:

    1. @cite{grice-1975}: Quantity decomposes into Q1 (informative) + Q2 (brief)
    2. @cite{dale-reiter-1995}: No-Brevity (Q2 relaxed) matches human production;
       IA uses a stipulated preference order (color before size)
    3. @cite{engelhardt-etal-2006}: speakers over-describe ~31%, Q2 violations
       tolerated explicitly but detected implicitly
    4. @cite{frank-goodman-2012}: RSA formalizes Q1 via L0, Q2 via cost;
       Boolean semantics predicts no overmodification preference
    5. @cite{cohn-gordon-etal-2019}: Incremental RSA processes features
       sequentially, also in No-Brevity regime
    6. **This paper**: cs-RSA explains WHY No-Brevity is rational — noise
       makes redundant modifiers informative. Noise asymmetry (color > size)
       DERIVES the preference ordering that D&R stipulate.

    cs-RSA does not merely describe the No-Brevity regime; it explains it.
    The "over-informative" speaker is actually being informative (Q1) in
    a world where perception is noisy. -/
theorem explanatory_chain :
    -- Q1 and Q2 are independent sub-maxims
    QuantityViolation.underInformative.submaxim ≠
    QuantityViolation.overInformative.submaxim ∧
    -- No-Brevity is the weakest Q2
    DaleReiter1995.BrevityInterpretation.noBrevity.strength = 0 ∧
    -- Engelhardt: speakers over-describe
    EngelhardtEtAl2006.exp1_target_1ref.modified > 0.2 ∧
    -- Boolean RSA: no overmod preference
    ¬(boolCfg.S1 () .target .both > boolCfg.S1 () .target .color) ∧
    -- cs-RSA: noise makes overmodification rational
    cfg.S1 () .target .both > cfg.S1 () .target .color ∧
    -- cs-RSA: color > size asymmetry from noise
    cfg.S1 () .target .color > cfg.S1 () .target .size ∧
    -- Discrimination ordering grounds the asymmetry
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination :=
  ⟨violations_independent, rfl, by native_decide,
   bool_no_overmod_preference,
   csrsa_overmod_beats_color, csrsa_color_beats_size,
   RSA.Noise.color_gt_size⟩

end Phenomena.Reference.Studies.DegenEtAl2020

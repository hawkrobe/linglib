import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Noise
import Linglib.Core.Inheritance
import Linglib.Phenomena.Reference.Studies.DaleReiter1995

/-!
# @cite{westerbeek-koolen-maes-2015}
@cite{dale-reiter-1995}

Stored Object Knowledge and the Production of Referring Expressions:
The Case of Color Typicality. *Frontiers in Psychology* 6, 935.

## Core Argument

Speakers mention color in referring expressions more often when an
object's color is atypical (blue banana) than when it is typical
(yellow banana), even when color is not necessary for unique
identification. This cannot be explained by physical salience (they
control for this computationally via Erdem & Erdem 2013) — it arises
from a **contrast with stored object knowledge**: the perceived color
deviates from the prototypical color stored in long-term memory.

The effect is proportional to degree of atypicality (continuous, not
binary) and is moderated by **color diagnosticity**: it is strongest
for high color-diagnostic objects (simple shapes like apples, where
color is a primary identifying feature) and weaker for low
color-diagnostic objects (complex shapes like lobsters, where shape
alone identifies the object).

## Experiments

**Experiment 1** (N = 43, 40 analysed after 3 excluded for audio
issues): Simple objects varying in color typicality. Speakers describe
target objects in 6-object visual scenes where color is never necessary
for disambiguation. Strong main effect of color typicality on color
mention rate. Pearson r(40) = −0.86 between typicality score and
proportion of color descriptions.

**Experiment 2** (N = 62 participants in 31 speaker–addressee pairs):
2 × 2 design crossing color typicality (typical / atypical) with
shape diagnosticity (high / low, i.e., complex / simple shapes).
Significant main effect of atypicality, and significant interaction:
the typicality effect is larger for low shape-diagnostic (= high
color-diagnostic, simple shape) objects.

## Architecture

The meaning function is constructed from two components:

1. **`typicalityφ`** — shared structure of the reference game:
   a 2 × 2 matrix parameterised by a single value, the bare noun's
   effectiveness for the target. All other cells are fixed.

2. **`bareEffectiveness`** — maps color typicality (from a `Prototype`)
   to recognition effectiveness: how well the bare noun identifies
   a target whose color has this typicality. Linear in typicality;
   even a completely atypical object has nonzero effectiveness
   (category membership is not zero, just degraded).

The composition `typicalityφ ∘ bareEffectiveness ∘ proto.typicality`
produces meaning functions grounded in stored knowledge by
construction.

## Verified Predictions

1. S1(withColor) is strictly decreasing in bare noun effectiveness
   (monotonicity theorem, general)
2. Atypical objects receive more color mention than typical objects
3. Color mention is preferred in both conditions, but more strongly
   for atypical
4. The color preference gap is larger for atypical than typical
5. Color diagnosticity interaction: the typicality effect is larger
   for high color-diagnostic (simple shape) objects
6. RSA prediction: color modifier preferred for atypical target
7. Meaning functions are derived from Prototype via bareEffectiveness
8. IA produces identical output for typical and atypical targets
   (preference order is static)
-/

set_option autoImplicit false

namespace WesterbeekKoolenMaes2015

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Objects in a referential display. The target is always of a unique
    type (e.g., the only banana among non-bananas), so color is never
    required for disambiguation. The question is whether the speaker
    *voluntarily* mentions the target's color. -/
inductive World where
  /-- Target object (e.g., the banana) -/
  | target
  /-- Distractor (different category, e.g., an apple) -/
  | distractor
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Referring expressions. The speaker can use a bare noun ("the
    banana") or add a color modifier ("the yellow/blue banana"). -/
inductive Utterance where
  /-- "the banana" — head noun only -/
  | bare
  /-- "the [color] banana" — color modifier + head noun -/
  | withColor
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. Typicality-Parameterised Meaning Function
-- ============================================================================

/-- Meaning function parameterised by the bare noun's effectiveness for
    the target. This is the single parameter that varies across
    typicality conditions — all other cells are fixed:

        | Utterance | target     | distractor |
        |-----------|------------|------------|
        | bare      | bareTarget | 1/10       |
        | withColor | 19/20      | 1/20       |

    The distractor values are fixed because distractor identity does
    not depend on the target's color. The `withColor` values are fixed
    because mentioning the actual color resolves any recognition
    mismatch regardless of typicality.

    The key architectural point: all condition-specific meaning
    functions are instances of this single constructor. The condition
    structure is explicit in the parameterisation rather than hidden
    in four separate case-by-case definitions. -/
def typicalityφ (bareTarget : ℚ) : Utterance → World → ℚ
  | .bare, .target => bareTarget
  | .bare, .distractor => 1/10
  | .withColor, .target => 19/20
  | .withColor, .distractor => 1/20

-- ============================================================================
-- §3. Stored Knowledge: Prototype and bareEffectiveness
-- ============================================================================

/-- Colors of the target banana. -/
inductive BananaColor where
  | yellow  -- typical
  | blue    -- atypical
  deriving DecidableEq, Repr

/-- Stored knowledge: yellow is the prototypical banana color.
    These values encode the contrast that drives color mention —
    a blue banana violates stored expectations. -/
def bananaPrototype : Core.Inheritance.Prototype BananaColor where
  category := .yellow
  typicality
    | .yellow => 9/10
    | .blue => 1/10

/-- Yellow (typical) is more prototypical than blue (atypical). -/
theorem typical_more_prototypical :
    bananaPrototype.moreTypical .yellow .blue = true := by native_decide

/-- Maps stored color typicality to bare noun recognition effectiveness.
    Linear: `bareEffectiveness(t) = 9/20 + t/2`.

    - When t = 9/10 (typical): bareEffectiveness = 9/10. The bare noun
      is highly effective — the listener imagines a yellow banana.
    - When t = 1/10 (atypical): bareEffectiveness = 1/2. The bare noun
      is degraded — the listener imagines yellow, but the object is blue.
    - The intercept 9/20 represents base category identification:
      even a maximally atypical color doesn't reduce effectiveness
      below 9/20 (it IS still a banana).
    - The slope 1/2 captures how much typicality boosts recognition. -/
def bareEffectiveness (colorTypicality : ℚ) : ℚ := 9/20 + colorTypicality / 2

theorem bareEff_typical : bareEffectiveness (9/10) = 9/10 := by unfold bareEffectiveness; ring
theorem bareEff_atypical : bareEffectiveness (1/10) = 1/2 := by unfold bareEffectiveness; ring

/-- bareEffectiveness is strictly increasing: higher color typicality
    → higher bare noun effectiveness. This is the first link in the
    chain Prototype → bareEffectiveness → typicalityφ → S1, and it
    ensures that typicality ordering is preserved through the transform. -/
theorem bareEffectiveness_strictMono (t₁ t₂ : ℚ) (h : t₁ < t₂) :
    bareEffectiveness t₁ < bareEffectiveness t₂ := by
  unfold bareEffectiveness; linarith

-- ============================================================================
-- §4. Condition-Specific Meaning Functions (Derived)
-- ============================================================================

/-- Meaning function for the **typical** color condition (e.g., yellow
    banana). Derived from the Prototype via bareEffectiveness:
    `typicalityφ (bareEffectiveness (bananaPrototype.typicality .yellow))`
    = `typicalityφ (9/10)`.

    φ(bare, target) = 9/10: the bare noun is highly effective because
    the listener's stored representation matches reality. -/
def φ_typical : Utterance → World → ℚ :=
  typicalityφ (bareEffectiveness (bananaPrototype.typicality .yellow))

/-- Meaning function for the **atypical** color condition (e.g., blue
    banana). Derived from the Prototype via bareEffectiveness:
    `typicalityφ (bareEffectiveness (bananaPrototype.typicality .blue))`
    = `typicalityφ (1/2)`.

    φ(bare, target) = 1/2: the bare noun is degraded because the
    listener imagines yellow but the object is blue. -/
def φ_atypical : Utterance → World → ℚ :=
  typicalityφ (bareEffectiveness (bananaPrototype.typicality .blue))

/-- Sanity check: φ_typical(bare, target) coincides numerically with
    the Prototype's typicality value. This is a consequence of the
    linear parameters (intercept = 9/20, slope = 1/2) chosen for
    `bareEffectiveness`, not a deep structural necessity. -/
theorem φ_typical_grounded :
    φ_typical .bare .target = bananaPrototype.typicality .yellow := by
  simp [φ_typical, typicalityφ, bareEffectiveness, bananaPrototype]; ring

/-- Grounding: the typical and atypical meaning functions differ only
    in the Prototype input — all other structure is shared. -/
theorem shared_structure :
    φ_typical .bare .distractor = φ_atypical .bare .distractor ∧
    φ_typical .withColor .target = φ_atypical .withColor .target ∧
    φ_typical .withColor .distractor = φ_atypical .withColor .distractor :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §5. L0 and S1 (ℚ-valued)
-- ============================================================================

/-- L0 posterior: φ(u,w) / Σ_{w'} φ(u,w'). -/
def L0_q (φ : Utterance → World → ℚ) (u : Utterance) (w : World) : ℚ :=
  φ u w / (φ u .target + φ u .distractor)

/-- S1 probability: L0(w|u) / Σ_{u'} L0(w|u'). With α = 1 and
    cost = 0 (No-Brevity), S1 is proportional to L0. -/
def S1_q (φ : Utterance → World → ℚ) (u : Utterance) (w : World) : ℚ :=
  L0_q φ u w / (L0_q φ .bare w + L0_q φ .withColor w)

-- ============================================================================
-- §6. Monotonicity: The General Principle
-- ============================================================================

/-! S1(withColor | target) is strictly decreasing in the bare noun's
effectiveness `t`. Algebraically, S1 = (190t+19)/(390t+19), whose
derivative is −3800/(390t+19)² < 0. Intuitively: a more effective
bare noun makes color mention less necessary, so S1 allocates less
probability to it.

All point predictions in §7–§9 are instances of this monotonicity. -/

/-- S1(withColor | target) as a closed-form function of bare noun
    effectiveness. Equivalent to `S1_q (typicalityφ t) .withColor .target`
    when denominators are non-zero (i.e., t > 0). -/
def S1_colorMention (t : ℚ) : ℚ := (190 * t + 19) / (390 * t + 19)

/-- **Equivalence**: S1_q at (withColor, target) equals the closed-form
    `S1_colorMention` for any `typicalityφ t` meaning function. This
    ensures the monotonicity theorem applies to all S1_q predictions,
    not just the specific parameter values checked below. -/
theorem S1_q_eq_S1_colorMention (t : ℚ) (h : 0 < t) :
    S1_q (typicalityφ t) .withColor .target = S1_colorMention t := by
  have h1 : t + 1 / 10 ≠ 0 := by linarith
  have h2 : (20 : ℚ) ≠ 0 := by norm_num
  have h3 : (10 : ℚ) ≠ 0 := by norm_num
  simp only [S1_q, L0_q, typicalityφ, S1_colorMention]
  field_simp
  ring

/-- S1_colorMention equals S1_q at the specific parameter values
    used in the model. (Corollaries of `S1_q_eq_S1_colorMention`.) -/
theorem S1_closed_typical :
    S1_q φ_typical .withColor .target = S1_colorMention (9/10) := by native_decide
theorem S1_closed_atypical :
    S1_q φ_atypical .withColor .target = S1_colorMention (1/2) := by native_decide

/-- **Monotonicity**: S1(withColor | target) is strictly decreasing in
    bare noun effectiveness. Higher typicality → more effective bare
    noun → less color mention.

    **Proof**: Cross-multiplying the fraction comparison reduces to
    `3800 · (t₂ − t₁) > 0`, which holds since `t₁ < t₂`. -/
theorem S1_colorMention_decreasing (t₁ t₂ : ℚ)
    (h₁ : 0 < t₁) (h₁₂ : t₁ < t₂) :
    S1_colorMention t₁ > S1_colorMention t₂ := by
  unfold S1_colorMention
  rw [gt_iff_lt, div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- Monotonicity instantiated at the three parameter values used in
    the model: 1/2 (atypical), 7/10 (low color-diag atypical), 9/10
    (typical). The ordering is strict. -/
theorem monotonicity_instances :
    S1_colorMention (1/2) > S1_colorMention (7/10) ∧
    S1_colorMention (7/10) > S1_colorMention (9/10) := by
  constructor <;> (unfold S1_colorMention; rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) (by norm_num)]; norm_num)

-- ============================================================================
-- §7. L0 Verification
-- ============================================================================

/-- L0(target | bare) = 9/10 in the typical condition. -/
theorem L0_typical_bare : L0_q φ_typical .bare .target = 9/10 := by native_decide

/-- L0(target | bare) = 5/6 in the atypical condition. Lower than
    typical (9/10) because stored color expectations create a mismatch. -/
theorem L0_atypical_bare : L0_q φ_atypical .bare .target = 5/6 := by native_decide

/-- L0(target | withColor) = 19/20 in both conditions. Color mention
    resolves any mismatch — this is fixed by construction in
    `typicalityφ`. -/
theorem L0_withColor_constant :
    L0_q φ_typical .withColor .target = 19/20 ∧
    L0_q φ_atypical .withColor .target = 19/20 := by
  constructor <;> native_decide

/-- The bare noun is more effective for typical than atypical targets. -/
theorem bare_better_for_typical :
    L0_q φ_typical .bare .target > L0_q φ_atypical .bare .target := by native_decide

-- ============================================================================
-- §8. Core Predictions
-- ============================================================================

/-- **Main prediction**: S1 allocates more probability to color mention
    for atypically colored objects than for typically colored objects.
    Instance of `S1_colorMention_decreasing` at t₁ = 1/2, t₂ = 9/10. -/
theorem atypical_more_color :
    S1_q φ_atypical .withColor .target > S1_q φ_typical .withColor .target := by
  native_decide

/-- In the typical condition, color mention is still slightly preferred
    (S1 > 0.5 for withColor). Even typical colors carry some signal. -/
theorem typical_color_preferred :
    S1_q φ_typical .withColor .target > S1_q φ_typical .bare .target := by
  native_decide

/-- In the atypical condition, color mention is more strongly preferred. -/
theorem atypical_color_strongly_preferred :
    S1_q φ_atypical .withColor .target > S1_q φ_atypical .bare .target := by
  native_decide

/-- The color preference gap is larger in the atypical condition. -/
theorem atypical_gap_larger :
    S1_q φ_atypical .withColor .target - S1_q φ_atypical .bare .target >
    S1_q φ_typical .withColor .target - S1_q φ_typical .bare .target := by
  native_decide

-- ============================================================================
-- §9. RSA Config (Atypical Condition)
-- ============================================================================

open RSA Real in
/-- RSA model for the atypical color condition. Demonstrates that the
    ℚ-valued predictions correspond to a genuine RSAConfig.

    Architecture: same as @cite{degen-etal-2020}'s cs-RSA — the only
    difference is the meaning function, which now varies with color
    typicality rather than with perceptual noise parameters. -/
noncomputable def atypicalCfg : RSAConfig Utterance World where
  meaning _ _ u w := ↑(φ_atypical u w)
  meaning_nonneg _ _ u w := by cases u <;> cases w <;> simp [φ_atypical, typicalityφ, bareEffectiveness, bananaPrototype] <;> norm_num
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

/-- RSA prediction: color modifier is preferred for the atypical target. -/
theorem rsa_atypical_color_preferred :
    atypicalCfg.S1 () .target .withColor > atypicalCfg.S1 () .target .bare := by
  rsa_predict

-- ============================================================================
-- §10. Color Diagnosticity Interaction (Experiment 2)
-- ============================================================================

/-! Experiment 2 crosses color typicality (typical / atypical) with
shape diagnosticity (high / low) in a 2 × 2 design.

Terminology mapping (the paper and our code use different axes):

    | Paper term              | Our term              | Shape    | Example  |
    |-------------------------|-----------------------|----------|----------|
    | Low shape diagnosticity | High color diagnostic | simple   | apple    |
    | High shape diagnosticity| Low color diagnostic  | complex  | lobster  |

The interaction: the typicality effect is LARGER for high color-diagnostic
(simple shape) objects, because color is their primary identifying
feature, so deviations from typical color are more disruptive.

The model captures this by varying the bare noun effectiveness at
the atypical level: for high color-diagnostic objects, atypical color
severely degrades the bare noun (1/2); for low color-diagnostic
objects, shape compensates and the bare noun remains fairly effective
(7/10). -/

/-- Meaning function for **low color-diagnostic** (complex shape)
    objects in the atypical color condition. φ(bare, target) = 7/10:
    higher than the high color-diagnostic atypical condition (1/2)
    because the distinctive shape compensates for the color mismatch. -/
def φ_lowColorDiag_atypical : Utterance → World → ℚ := typicalityφ (7/10)

/-- S1 color mention rates for all four conditions of Exp 2:

    | Condition                         | bareTarget | S1(withColor) |
    |-----------------------------------|------------|---------------|
    | High color-diag + typical         | 9/10       | 19/37         |
    | High color-diag + atypical        | 1/2        | 57/107        |
    | Low color-diag + typical          | 9/10       | 19/37         |
    | Low color-diag + atypical         | 7/10       | 38/73         | -/
theorem s1_values :
    S1_q φ_typical .withColor .target = 19/37 ∧
    S1_q φ_atypical .withColor .target = 57/107 ∧
    S1_q (typicalityφ (9/10)) .withColor .target = 19/37 ∧
    S1_q φ_lowColorDiag_atypical .withColor .target = 38/73 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Interaction**: the typicality effect on color mention is larger
    for high color-diagnostic (simple shape) objects.

    High color-diag gap: 57/107 − 19/37 = 76/3959
    Low color-diag gap:  38/73  − 19/37 = 19/2701

    This captures the paper's Exp 2 finding: "the effect of typicality
    on using color in a referring expression was larger for [low shape-
    diagnostic] objects" — i.e., objects where color is more diagnostic
    and deviations from typical color are more disruptive. -/
theorem diagnosticity_interaction :
    S1_q φ_atypical .withColor .target -
      S1_q φ_typical .withColor .target >
    S1_q φ_lowColorDiag_atypical .withColor .target -
      S1_q φ_typical .withColor .target := by
  native_decide

/-- All four conditions prefer color mention, but at different rates. -/
theorem all_prefer_color :
    S1_q φ_typical .withColor .target > S1_q φ_typical .bare .target ∧
    S1_q φ_atypical .withColor .target > S1_q φ_atypical .bare .target ∧
    S1_q (typicalityφ (9/10)) .withColor .target > S1_q (typicalityφ (9/10)) .bare .target ∧
    S1_q φ_lowColorDiag_atypical .withColor .target > S1_q φ_lowColorDiag_atypical .bare .target := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §11. Experimental Data
-- ============================================================================

/-- Mixed-effects logistic regression result. -/
structure RegressionResult where
  β : Float
  se : Float
  significant : Bool
  deriving Repr

/-- Exp 1 main effect: color typicality predicts color mention.
    Predictor is typicality (higher = more typical), so β is negative:
    more typical → less color mention. β = −2.36, SE = 0.25, p < .001.
    N = 43 participants (40 analysed; 3 excluded for audio issues). -/
def exp1_typicality : RegressionResult :=
  { β := -2.36, se := 0.25, significant := true }

/-- Exp 1: Pearson correlation between typicality score and proportion
    of color descriptions, r(40) = −0.86, p < .001 (Figure 3). -/
def exp1_correlation : Float := -0.86

theorem exp1_typicality_negative :
    exp1_typicality.β < 0 := by native_decide

theorem exp1_strong_correlation :
    exp1_correlation < -0.80 := by native_decide

/-- Exp 2 descriptive rates (collapsed across shape diagnosticity):
    73.5% of references to atypically colored targets contained color
    vs 13.1% for typically colored targets (p. 9). -/
def exp2_atypical_rate : Float := 0.735
def exp2_typical_rate : Float := 0.131

theorem exp2_atypical_exceeds_typical :
    exp2_atypical_rate > exp2_typical_rate := by native_decide

/-- Exp 2 main effect: color atypicality predicts color mention.
    Note sign flip vs Exp 1: Exp 2 codes the predictor as *atypicality*
    (higher = more atypical), so β is positive. Same direction:
    more atypical → more color mention.
    β = 3.55, SE = 0.96, p < .001.
    N = 62 participants (31 speaker–addressee pairs, 31 speakers
    analysed). -/
def exp2_atypicality : RegressionResult :=
  { β := 3.55, se := 0.96, significant := true }

/-- Exp 2 interaction: color atypicality × shape diagnosticity.
    β = −0.56, SE = 0.32, p = .010. Negative: the atypicality effect
    *decreases* as shape diagnosticity increases (complex shapes reduce
    the importance of color). -/
def exp2_interaction : RegressionResult :=
  { β := -0.56, se := 0.32, significant := true }

/-- Both experiments find the same directional effect despite opposite
    predictor coding: more atypical → more color mention. -/
theorem consistent_direction :
    exp1_typicality.β < 0 ∧ exp2_atypicality.β > 0 := by
  constructor <;> native_decide

-- ============================================================================
-- §12. Prototype Grounding
-- ============================================================================

/-- **Full-chain monotonicity**: higher Prototype typicality → higher
    bareEffectiveness → lower S1(withColor). Each step is derived:
    1. `moreTypical` from Prototype (stored knowledge)
    2. `bareEffectiveness_strictMono` (strictly increasing linear map)
    3. `S1_colorMention_decreasing` (strictly decreasing rational function)
    The composition reverses the ordering: more typical → less color mention. -/
theorem prototype_predicts_color_mention :
    bananaPrototype.moreTypical .yellow .blue = true ∧
    bareEffectiveness (bananaPrototype.typicality .blue) <
      bareEffectiveness (bananaPrototype.typicality .yellow) ∧
    S1_q φ_typical .withColor .target < S1_q φ_atypical .withColor .target :=
  ⟨typical_more_prototypical,
   bareEffectiveness_strictMono _ _ (by native_decide),
   atypical_more_color⟩

-- ============================================================================
-- §13. Bridge: IA Typicality-Blindness
-- ============================================================================

/-! The Incremental Algorithm iterates through a fixed preference-ordered
attribute list. We demonstrate concretely that the IA produces **identical
output** for a typically and atypically colored target in the same scene
layout, because the preference order is static. -/

section IA
open DaleReiter1995

/-- Target: a yellow banana (typical color). -/
def typicalTarget : KBEntity :=
  ⟨[(.headNoun, "banana"), (.modifier .color, "yellow")]⟩

/-- Target: a blue banana (atypical color). -/
def atypicalTarget : KBEntity :=
  ⟨[(.headNoun, "banana"), (.modifier .color, "blue")]⟩

/-- Distractor: an apple (different category). -/
def appleDistractor : KBEntity :=
  ⟨[(.headNoun, "apple"), (.modifier .color, "red")]⟩

/-- Preference order: type first, then color. -/
def prefOrder : List REGAttribute := [.headNoun, .modifier .color]

/-- The IA produces the same attributes for both typical and atypical
    targets: {type = banana}. Color is included in neither case
    because "banana" alone rules out the apple distractor — the IA
    never reaches color in the preference order.

    The IA is structurally blind to typicality: it does not know that
    "blue banana" would be more helpful to the addressee than "yellow
    banana." cs-RSA captures this through the meaning function. -/
theorem ia_same_output :
    incrementalAlgorithm typicalTarget [appleDistractor] prefOrder =
    incrementalAlgorithm atypicalTarget [appleDistractor] prefOrder := by
  native_decide

/-- Both IA runs succeed (the single distractor is ruled out by type). -/
theorem ia_both_succeed :
    iaSuccess typicalTarget [appleDistractor] prefOrder ∧
    iaSuccess atypicalTarget [appleDistractor] prefOrder := by
  constructor <;> native_decide

/-- The IA produces a single attribute (type = banana) and omits color
    entirely. cs-RSA, by contrast, varies the probability of color
    mention with typicality. -/
theorem ia_vs_csrsa :
    incrementalAlgorithm typicalTarget [appleDistractor] prefOrder =
      [(.headNoun, "banana")] ∧
    S1_q φ_atypical .withColor .target > S1_q φ_typical .withColor .target :=
  ⟨by native_decide, atypical_more_color⟩

end IA

-- ============================================================================
-- §14. Bridge: Noise and Typicality Are Complementary
-- ============================================================================

/-! @cite{degen-etal-2020}'s cs-RSA derives the color > size asymmetry
from noise discrimination parameters. This paper's contribution is
orthogonal: typicality modulates the meaning function **within** a single
feature dimension (color), varying the effectiveness of the bare noun
by how well the perceived color matches stored expectations. Both
mechanisms operate through continuous semantics. -/

/-- Noise and typicality both modulate continuous semantics:
    - Noise: color discrimination > size discrimination (across features)
    - Typicality: atypical color → more color mention (within a feature)
    Both are necessary: noise explains color > size; typicality explains
    atypical > typical within color. -/
theorem noise_and_typicality_complementary :
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    S1_q φ_atypical .withColor .target > S1_q φ_typical .withColor .target :=
  ⟨RSA.Noise.color_gt_size, atypical_more_color⟩

end WesterbeekKoolenMaes2015

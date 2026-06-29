import Linglib.Tactics.RSAPredict
import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.RSA.Channel
import Linglib.Pragmatics.GriceanMaxims
import Linglib.Studies.DaleReiter1995

/-!
# [degen-etal-2020]
[frank-goodman-2012] [dale-reiter-1995] [engelhardt-etal-2006]
[grice-1975] [kursat-degen-2021] [westerbeek-koolen-maes-2015]

When Redundancy Is Useful: A Bayesian Approach to "Overinformative" Referring
Expressions. *Psychological Review* 127(4), 591–621.

## Core Argument

Standard RSA with Boolean semantics (φ ∈ {0,1}) predicts no preference for
overmodified referring expressions — if "small" alone identifies the target,
adding "blue" is literally uninformative. But speakers routinely overmodify
(~31% in [engelhardt-etal-2006]), with color mentioned redundantly
more often than size.

cs-RSA replaces Boolean denotations with **continuous semantics**: φ(u, o) ∈ [0,1]
via a **Product of Experts** (PoE) model. Each feature dimension acts as an
independent noisy channel:

    φ(u, o) = φ_size(u, o) · φ_color(u, o)

where φ_color = match_val if colors agree, mismatch_val otherwise (and
similarly for size). The **asymmetry** between color and size arises from
differing noise levels:

    color: match = 0.99, mismatch = 0.01 → discrimination = 0.98
    size:  match = 0.80, mismatch = 0.20 → discrimination = 0.60

Adding a redundant color modifier (high discrimination) sharpens the listener's
posterior more than adding redundant size would → speakers overmodify with
color more.

## Scene (§2 demonstration)

Three objects: {big blue pin, big red pin, small blue pin (TARGET)}.

    | Object    | Size  | Color |
    |-----------|-------|-------|
    | bigBlue   | big   | blue  |
    | bigRed    | big   | red   |
    | smallBlue | small | blue  |  ← TARGET

- **Size-sufficient**: only the target is small, so "small" uniquely identifies
- **Color-redundant**: two objects are blue, so "blue" alone does not identify

Seven utterances: {"big", "small", "blue", "red", "big blue", "big red",
"small blue"} (all followed by implicit "pin").

## Architecture

    L0(o|u) ∝ φ(u, o)
    S1(u|w) ∝ exp(α · log L0(w|u) − β_c · cost(u))

BDA-fitted cost β_c ≈ 0, placing the model in the **No-Brevity** regime.
With α = 1 and β_c = 0, S1(u|w) ∝ L0(w|u).

NOTE: The paper's Table 2 uses L0(o|u) ∝ exp(φ(u,o)) (WebPPL `factor`
convention). Our formalization uses L0 ∝ φ (matching the paper's eq. 1
directly). Both give identical S1 orderings since exp is monotone; the
numerical L0 values differ but the qualitative predictions are the same.

## Verified Predictions

1. cs-RSA: S1 prefers overmodified "small blue" > sufficient "small"
2. cs-RSA: sufficient "small" > redundant "blue" (size principle)
3. cs-RSA: full 7-utterance S1 ordering at target
4. Boolean RSA: no overmodification preference (smallBlue tied with small)
5. Connection: cost = 0 ↔ [dale-reiter-1995] No-Brevity (strength 0)
6. Connection: noise discrimination ordering grounds the asymmetry
7. Connection: explains [engelhardt-etal-2006]'s ~31% over-description
8. Exp 2: typicality predicts color modifier production (β = −4.17, p < .0001)
9. Exp 3: informativeness hierarchy predicts nominal choice (β = 2.11, p < .0001)
10. Exp 3: typicality predicts subordinate use (β = 4.82, p < .001)
11. Bridge: noise (adjectives) and typicality (nouns) are parallel mechanisms

## Verified Data

**Exp 1** (§3): main effect of sufficient property β = 3.54, SE = .22,
p < .0001; interaction β = 2.26, SE = .74, p < .003. BDA-fitted noise
parameters (Figure 10 caption): MAP x_color = .88, MAP x_size = .79,
confirming color > size discrimination. Fitted β_c values near zero.

**Exp 2** (§4.3): typicality β = −4.17, SE = .45, p < .0001;
informativeness β = −5.56, SE = .33, p < .0001; color competitor
β = 0.71, SE = .16, p < .0001.

**Exp 3** (§5.2): sub necessary β = 2.11, SE = .17, p < .0001; basic
vs super β = .60, SE = .15, p < .0001; typicality β = 4.82, SE = 1.35,
p < .001; length β = −.95, SE = .27, p < .001; frequency β = .08,
SE = .11, NS. BDA (§5.3, Figure 19): β_fixed MAP = 0.004,
β_i MAP = 19.8, β_t MAP = 0.57, β_F MAP = 0.02, β_L MAP = 2.69.
-/

set_option autoImplicit false

namespace DegenEtAl2020

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Objects in the §2 demonstration scene: three pins varying in size and
    color. The target is the small blue pin. -/
inductive World where
  /-- Big blue pin -/
  | bigBlue
  /-- Big red pin -/
  | bigRed
  /-- Small blue pin (TARGET) -/
  | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Referring expressions available to the speaker. Each is an adjective
    combination followed by the implicit head noun "pin":
    - Single: "big", "small", "blue", "red"
    - Complex: "big blue", "big red", "small blue" -/
inductive Utterance where
  /-- "big pin" — size only -/
  | big
  /-- "small pin" — size only (SUFFICIENT for target) -/
  | small
  /-- "blue pin" — color only (REDUNDANT: two objects are blue) -/
  | blue
  /-- "red pin" — color only -/
  | red
  /-- "big blue pin" — size + color -/
  | bigBlue
  /-- "big red pin" — size + color -/
  | bigRed
  /-- "small blue pin" — size + color (OVERMODIFIED) -/
  | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The target object in this scene. -/
abbrev target : World := .smallBlue

-- ============================================================================
-- §2. Scene Properties
-- ============================================================================

/-- Size is sufficient: only one object (the target) is small. -/
theorem size_sufficient :
    ∀ w : World, w ≠ .smallBlue → (w = .bigBlue ∨ w = .bigRed) := by
  intro w h; cases w <;> simp_all

/-- Color is NOT sufficient: two objects share the target's color (blue). -/
theorem color_not_sufficient :
    ∃ w : World, w ≠ target ∧ w = .bigBlue :=
  ⟨.bigBlue, by decide, rfl⟩

-- ============================================================================
-- §3. Continuous Semantics (cs-RSA)
-- ============================================================================

/-- Continuous semantic value φ(u, o) via Product of Experts.

    Each feature dimension contributes a noisy channel value directly
    from the `RSA.Noise` module's standard parameters:

    - Single adjective: φ = channel value for that dimension
    - Complex adjective: φ = product of per-dimension channels (PoE)

    | Utterance    | bigBlue          | bigRed           | smallBlue         |
    |--------------|------------------|------------------|-------------------|
    | big          | sizeMatch (0.80) | sizeMatch (0.80) | sizeMismatch (0.20)|
    | small        | sizeMismatch     | sizeMismatch     | sizeMatch (0.80)  |
    | blue         | colorMatch (0.99)| colorMismatch    | colorMatch (0.99) |
    | red          | colorMismatch    | colorMatch (0.99)| colorMismatch     |
    | big blue     | sM·cM (0.792)   | sM·cMM (0.008)  | sMM·cM (0.198)   |
    | big red      | sM·cMM (0.008)  | sM·cM (0.792)   | sMM·cMM (0.002)  |
    | small blue   | sMM·cM (0.198)  | sMM·cMM (0.002) | sM·cM (0.792)    |

    The noise parameters are the §2 demonstration values from
    [degen-etal-2020], imported from `RSA.Noise`. -/
def φ : Utterance → World → ℚ
  -- single size adjectives
  | .big, .bigBlue => RSA.Noise.sizeMatch
  | .big, .bigRed => RSA.Noise.sizeMatch
  | .big, .smallBlue => RSA.Noise.sizeMismatch
  | .small, .bigBlue => RSA.Noise.sizeMismatch
  | .small, .bigRed => RSA.Noise.sizeMismatch
  | .small, .smallBlue => RSA.Noise.sizeMatch
  -- single color adjectives
  | .blue, .bigBlue => RSA.Noise.colorMatch
  | .blue, .bigRed => RSA.Noise.colorMismatch
  | .blue, .smallBlue => RSA.Noise.colorMatch
  | .red, .bigBlue => RSA.Noise.colorMismatch
  | .red, .bigRed => RSA.Noise.colorMatch
  | .red, .smallBlue => RSA.Noise.colorMismatch
  -- complex: Product of Experts (size × color)
  | .bigBlue, .bigBlue => RSA.Noise.sizeMatch * RSA.Noise.colorMatch
  | .bigBlue, .bigRed => RSA.Noise.sizeMatch * RSA.Noise.colorMismatch
  | .bigBlue, .smallBlue => RSA.Noise.sizeMismatch * RSA.Noise.colorMatch
  | .bigRed, .bigBlue => RSA.Noise.sizeMatch * RSA.Noise.colorMismatch
  | .bigRed, .bigRed => RSA.Noise.sizeMatch * RSA.Noise.colorMatch
  | .bigRed, .smallBlue => RSA.Noise.sizeMismatch * RSA.Noise.colorMismatch
  | .smallBlue, .bigBlue => RSA.Noise.sizeMismatch * RSA.Noise.colorMatch
  | .smallBlue, .bigRed => RSA.Noise.sizeMismatch * RSA.Noise.colorMismatch
  | .smallBlue, .smallBlue => RSA.Noise.sizeMatch * RSA.Noise.colorMatch

/-- φ is non-negative for all utterance-world pairs. -/
theorem φ_nonneg (u : Utterance) (w : World) : 0 ≤ φ u w := by
  cases u <;> cases w <;> simp [φ, RSA.Noise.colorMatch, RSA.Noise.colorMismatch,
    RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch] <;> norm_num

/-- φ uses the same noise parameters as the `RSA.Noise` module —
    by construction, not by bridge theorem. -/
theorem φ_grounded_in_noise :
    φ .blue .smallBlue = RSA.Noise.colorMatch ∧
    φ .blue .bigRed = RSA.Noise.colorMismatch ∧
    φ .small .smallBlue = RSA.Noise.sizeMatch ∧
    φ .small .bigBlue = RSA.Noise.sizeMismatch :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §3b. Product of Experts Decomposition
-- ============================================================================

/-- Complex utterances decompose as products of per-feature channel values —
    the concrete Product of Experts model from [degen-etal-2020] §2.
    Each feature dimension contributes an independent noisy channel;
    the combined φ is their product. -/
theorem φ_product_of_experts :
    (∀ w, φ .bigBlue w = φ .big w * φ .blue w) ∧
    (∀ w, φ .bigRed w = φ .big w * φ .red w) ∧
    (∀ w, φ .smallBlue w = φ .small w * φ .blue w) := by
  refine ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩ <;> cases w <;> rfl

-- ============================================================================
-- §4. cs-RSA Config (α = 1, cost = 0)
-- ============================================================================

open RSA Real in
/-- cs-RSA model for the overmodification reference game.

    - **Meaning**: continuous PoE semantics φ(u,o) ∈ [0,1]
    - **S1**: gated exp(α · log L0), equivalent to L0^α with zero-gating
    - **α** = 1 (the paper BDA-fits α; we use 1 for qualitative predictions)
    - **Cost** = 0 (No-Brevity regime; paper's BDA estimates: β_c ≈ 0)

    The continuous meaning function is the key innovation: redundant modifiers
    carry non-zero information because noise channels are imperfect. The S1
    scoring pattern is the same as [frank-goodman-2012] — only the
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
-- §5. L0 Verification
-- ============================================================================

/-- L0 posterior computed directly from φ (ℚ-valued, for verification).
    L0(w|u) = φ(u,w) / Σ_w' φ(u,w'). These are the values under L0 ∝ φ
    (our formalization). The paper's Table 2 uses L0 ∝ exp(φ) (WebPPL
    convention); the orderings are the same but the numbers differ. -/
def L0_q (u : Utterance) (w : World) : ℚ :=
  φ u w / (φ u .bigBlue + φ u .bigRed + φ u .smallBlue)

/-- L0(target | "small") = 2/3. Size is sufficient: sizeMatch = 4/5
    gives the target a much higher score than the distractors (sizeMismatch
    = 1/5 each), but not perfect (unlike Boolean L0 = 1). -/
theorem L0_small_target : L0_q .small target = 2/3 := by
  norm_num [L0_q, φ, RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch,
    RSA.Noise.colorMatch, RSA.Noise.colorMismatch]

/-- L0(target | "small blue") = 99/124. The redundant color modifier
    sharpens the posterior from 2/3 to 99/124 ≈ 0.798. The improvement
    comes from the PoE: color's high-discrimination channel (0.98) adds
    substantial signal on top of size's moderate discrimination (0.60). -/
theorem L0_smallBlue_target : L0_q .smallBlue target = 99/124 := by
  norm_num [L0_q, φ, RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch,
    RSA.Noise.colorMatch, RSA.Noise.colorMismatch]

/-- The overmodified form sharpens L0: L0(target | "small blue") >
    L0(target | "small"). This is the core mechanism — redundant modifiers
    carry real information through the noise channel. -/
theorem L0_overmod_sharpens :
    L0_q .smallBlue target > L0_q .small target := by
  norm_num [L0_q, φ, RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch,
    RSA.Noise.colorMatch, RSA.Noise.colorMismatch]

/-- L0(target | "blue") = 99/199. Color is redundant: two objects are blue
    (bigBlue and smallBlue), so the listener assigns equal probability
    to both. The target gets 99/199 ≈ 0.497, just under 1/2. -/
theorem L0_blue_target : L0_q .blue target = 99/199 := by
  norm_num [L0_q, φ, RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch,
    RSA.Noise.colorMatch, RSA.Noise.colorMismatch]

-- ============================================================================
-- §6. Core Prediction: cs-RSA Prefers Overmodification
-- ============================================================================

/-- **Main result**: cs-RSA's S1 strictly prefers the overmodified form
    "small blue pin" over the size-sufficient "small pin."

    Mechanism: "small" gives L0(target) = 2/3 (sizeMatch/(2·sizeMismatch
    + sizeMatch)). Adding "blue" sharpens to L0(target) = 99/124 ≈ 0.798
    via the PoE. With cost = 0, there is no penalty for the extra modifier,
    so S1 strictly prefers the more informative form.

    This is the paper's central result: overmodification is RATIONAL under
    noisy perception, not a violation of Grice's Brevity maxim. -/
theorem csrsa_overmod_preferred :
    cfg.S1 () target .smallBlue > cfg.S1 () target .small := by
  rsa_predict

-- ============================================================================
-- §7. Core Prediction: Sufficient > Redundant
-- ============================================================================

/-- The sufficient modifier "small" beats the redundant modifier "blue."
    "small" gives L0(target) = 2/3; "blue" gives L0(target) = 99/199 ≈ 0.497.
    Size uniquely identifies the target, while color does not.

    This is the **size principle** ([frank-goodman-2012]): utterances
    with smaller extensions are more informative. "small" applies to 1 object
    (under Boolean denotation) while "blue" applies to 2. -/
theorem csrsa_sufficient_beats_redundant :
    cfg.S1 () target .small > cfg.S1 () target .blue := by
  rsa_predict

-- ============================================================================
-- §8. Full S1 Ordering
-- ============================================================================

/-- Complete S1 ordering for the target (smallBlue):

    smallBlue > small > blue > bigBlue > big > red > bigRed

    - smallBlue (overmodified): highest — both channels correct + PoE sharpening
    - small (sufficient): size uniquely identifies
    - blue (redundant): color partially identifies (2 of 3 objects)
    - bigBlue (wrong size, right color): wrong on the sufficient dimension
    - big (wrong size): only size channel, wrong direction
    - red (wrong color): only color channel, wrong direction
    - bigRed (wrong everything): both channels wrong, PoE suppresses -/
theorem csrsa_full_ordering :
    cfg.S1 () target .smallBlue > cfg.S1 () target .small ∧
    cfg.S1 () target .small > cfg.S1 () target .blue ∧
    cfg.S1 () target .blue > cfg.S1 () target .bigBlue ∧
    cfg.S1 () target .bigBlue > cfg.S1 () target .big ∧
    cfg.S1 () target .big > cfg.S1 () target .red ∧
    cfg.S1 () target .red > cfg.S1 () target .bigRed :=
  ⟨csrsa_overmod_preferred, csrsa_sufficient_beats_redundant,
   by rsa_predict, by rsa_predict, by rsa_predict, by rsa_predict⟩

-- ============================================================================
-- §9. Boolean Baseline: No Overmodification Preference
-- ============================================================================

/-- Boolean (zero-noise) semantic value. In the zero-noise limit, φ ∈ {0,1}:
    a feature either matches perfectly (1) or not at all (0).

    Key difference from cs-RSA: "small" gives L0(target) = 1 (perfect
    identification), so adding "blue" provides ZERO additional information.
    The overmodified and sufficient forms are equally informative. -/
def φ_bool : Utterance → World → ℚ
  -- single size adjectives
  | .big, .bigBlue => 1     | .big, .bigRed => 1     | .big, .smallBlue => 0
  | .small, .bigBlue => 0   | .small, .bigRed => 0   | .small, .smallBlue => 1
  -- single color adjectives
  | .blue, .bigBlue => 1    | .blue, .bigRed => 0    | .blue, .smallBlue => 1
  | .red, .bigBlue => 0     | .red, .bigRed => 1     | .red, .smallBlue => 0
  -- complex: Boolean AND (PoE with {0,1} channels)
  | .bigBlue, .bigBlue => 1 | .bigBlue, .bigRed => 0 | .bigBlue, .smallBlue => 0
  | .bigRed, .bigBlue => 0  | .bigRed, .bigRed => 1  | .bigRed, .smallBlue => 0
  | .smallBlue, .bigBlue => 0 | .smallBlue, .bigRed => 0 | .smallBlue, .smallBlue => 1

/-- Boolean semantics values are in {0, 1}. -/
theorem φ_bool_values (u : Utterance) (w : World) :
    φ_bool u w = 0 ∨ φ_bool u w = 1 := by
  cases u <;> cases w <;> simp [φ_bool]

open RSA Real in
/-- Standard RSA with Boolean semantics (φ ∈ {0,1}).
    Same architecture as cs-RSA but with zero noise. This is the
    [frank-goodman-2012] model applied to the same scene. -/
noncomputable def boolCfg : RSAConfig Utterance World where
  meaning _ _ u w := ↑(φ_bool u w)
  meaning_nonneg _ _ u w := by cases u <;> cases w <;> simp [φ_bool]
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
    better than "small pin." Both give L0(target) = 1.0 (perfect
    identification), so adding "blue" provides zero information. -/
theorem bool_no_overmod_preference :
    ¬(boolCfg.S1 () target .smallBlue > boolCfg.S1 () target .small) := by
  rsa_predict

-- ============================================================================
-- §10. The Contrast: Noise Makes the Difference
-- ============================================================================

/-- **The contrast**: cs-RSA predicts overmodification where Boolean RSA
    does not. Noise is the key ingredient.

    Both models agree that "small" (sufficient, extension size 1) beats
    "blue" (redundant, extension size 2) — that is just the size principle
    from [frank-goodman-2012]. But they DISAGREE on whether adding
    "blue" to "small" helps:

    | Prediction              | cs-RSA  | Boolean |
    |-------------------------|---------|---------|
    | overmod > sufficient    | ✓       | ✗       |

    cs-RSA: L0(target|"small blue") = 99/124 > L0(target|"small") = 2/3
    Boolean: L0(target|"small blue") = L0(target|"small") = 1 -/
theorem noise_makes_the_difference :
    -- cs-RSA: overmodification helps
    cfg.S1 () target .smallBlue > cfg.S1 () target .small ∧
    -- Boolean: overmodification doesn't help
    ¬(boolCfg.S1 () target .smallBlue > boolCfg.S1 () target .small) :=
  ⟨csrsa_overmod_preferred, bool_no_overmod_preference⟩

/-! ### Empirical findings (Exp 1)

The Exp 1 mixed-effects regression (main effect of sufficient property β = 3.54,
SE = .22, p < .0001; scene-variation × property interaction β = 2.26, SE = .74,
p < .003) and the BDA-fitted parameters (MAP x_color = .88, HDI [.85, .92];
x_size = .79, HDI [.76, .80]; near-zero costs β_c ≈ .02/.03) are recorded in the
module docstring's *Verified Data*. These are empirical effect sizes / fitted
values, not model-derived quantities, so they live in prose rather than as Lean
data — the model-side content is the structural predictions
`csrsa_overmod_preferred` and `noise_grounds_asymmetry`. -/

-- ============================================================================
-- §13. Bridge: No-Brevity Regime
-- ============================================================================

open Pragmatics.GriceanMaxims

/-- cs-RSA operates in the No-Brevity regime: cost = 0, so there is no
    penalty for longer utterances (empirically confirmed: fitted β_c ≈ 0).
    This matches [dale-reiter-1995]'s No Brevity interpretation
    (the weakest Q2, strength = 0).

    The insight: No-Brevity is not just computationally convenient — it
    is **rational** when perception is noisy. Redundant modifiers carry
    real information through the noise channel, so omitting them harms
    the listener. Over-description is not a violation of Q2; it is Q1
    (be informative) operating in a noisy world.

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
-- §14. Bridge: Noise Discrimination Ordering
-- ============================================================================

/-- The color > size > material discrimination ordering from `RSA.Noise`
    directly predicts the overmodification ordering. cs-RSA's meaning
    function φ uses these noise values by construction (not by coincidence):
    `φ .blue .smallBlue = RSA.Noise.colorMatch`. -/
theorem noise_grounds_asymmetry :
    -- φ is grounded in RSA.Noise (structural, not coincidental)
    φ .blue .smallBlue = RSA.Noise.colorMatch ∧
    φ .small .smallBlue = RSA.Noise.sizeMatch ∧
    -- The discrimination ordering predicts color > size overmod
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination ∧
    -- The full ordering extends to material
    RSA.Noise.sizeDiscrimination > RSA.Noise.materialDiscrimination :=
  ⟨rfl, rfl, RSA.Noise.color_gt_size, RSA.Noise.size_gt_material⟩

-- ============================================================================
-- §15. Bridge: Explains Engelhardt et al. (2006)
-- ============================================================================

/-! cs-RSA explains the puzzle from [engelhardt-etal-2006]: speakers
over-describe ~31% of the time and listeners tolerate it (Q2 violations
accepted), yet implicitly detect the redundancy. cs-RSA's answer: over-description
is not a Q2 violation at all — in a noisy world redundant modifiers are genuinely
informative (Q1). The model-side claim is exactly `csrsa_overmod_preferred`
(overmodification raises the literal listener's posterior); the ~31% production
rate and the tolerated-but-detected judgment pattern are empirical anchors
recorded in the module docstring, not Lean data. -/

-- ============================================================================
-- §16. Bridge: Explanatory Chain
-- ============================================================================

/-- The explanatory chain from Gricean maxims to empirical overmodification:

    1. [grice-1975]: Quantity decomposes into Q1 (informative) + Q2 (brief)
    2. [dale-reiter-1995]: No-Brevity (Q2 relaxed) matches human production;
       IA uses a stipulated preference order (color before size)
    3. [engelhardt-etal-2006]: speakers over-describe ~31%, Q2 violations
       tolerated explicitly but detected implicitly
    4. [frank-goodman-2012]: RSA formalizes Q1 via L0, Q2 via cost;
       Boolean semantics predicts no overmodification preference
    5. **This paper**: cs-RSA explains WHY No-Brevity is rational — noise
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
    -- Boolean RSA: no overmod preference
    ¬(boolCfg.S1 () target .smallBlue > boolCfg.S1 () target .small) ∧
    -- cs-RSA: noise makes overmodification rational
    cfg.S1 () target .smallBlue > cfg.S1 () target .small ∧
    -- Discrimination ordering grounds the asymmetry
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination :=
  ⟨violations_independent, rfl,
   bool_no_overmod_preference, csrsa_overmod_preferred,
   RSA.Noise.color_gt_size⟩

-- ============================================================================
-- §17. Typicality: Continuous Noun Semantics (§4–§5)
-- ============================================================================

/-! The cs-RSA framework extends from modifier adjectives to head nouns via
**typicality**. Just as noise parameters replace Boolean feature matching
with continuous values for adjectives:

    φ_adj(u, o) = match/mismatch ∈ [0,1]

typicality replaces Boolean category membership for nouns:

    φ_noun(u, o) = typicality(o, category(u)) ∈ [0,1]

Both instantiate the same pattern: L(u,o) ∈ [0,1] instead of L(u,o) ∈ {0,1}.
Noise captures perceptual uncertainty about features; typicality captures
categorization uncertainty about type membership. The key insight is that
continuous semantics is not specific to adjective modification — it applies
whenever perception or categorization is graded rather than crisp.

The paper tests this in two experiments:

- **Exp 2** (§4): Color typicality affects modifier production. Atypical
  colors (blue banana) are mentioned MORE than typical colors (yellow banana).
- **Exp 3** (§5): Typicality affects head noun choice across taxonomic
  levels (subordinate, basic, superordinate). -/

-- ============================================================================
-- §18. Experiment 2: Color Typicality (§4)
-- ============================================================================

/-! Exp 2 (§4.3) confirms the typicality account of color mention: more typical
color → less color mention (β = −4.17, SE = .45), overinformative color → less
mention (β = −5.56, SE = .33), and an absent color competitor → more mention
(β = 0.71, SE = .16); all p < .0001. The negative typicality effect is the
within-feature analogue of the cross-feature color>size asymmetry: high-typicality
values are already expected, so mentioning them adds little information.
[westerbeek-koolen-maes-2015] independently found the same direction (β = −2.36)
with a 42-object stimulus set. These are empirical effect sizes (recorded in the
module docstring); the model-side parallel — a graded `φ_typ ∈ [0,1]` plays for
nouns the role noise plays for adjectives — is realized structurally below
(`φ_typ`, `nominal_overspec_preferred`, `typicality_makes_the_difference`). -/

-- ============================================================================
-- §19. Experiment 2: Model Evaluation (§4.4)
-- ============================================================================

/-! The model evaluation for Exp 2 compares three semantic specifications:

1. **Empirical typicality only** (β_fixed = 0): meaning function uses
   empirically elicited typicality ratings directly
2. **Type-level Boolean only** (β_fixed = 1): meaning function uses
   inferred match/mismatch values per type (as in Exp 1)
3. **Interpolation** (β_fixed ∈ [0,1]): weighted mix of empirical and
   type-level values

The BDA finds β_fixed MAP → 0: empirical typicality strongly dominates
Boolean type-level semantics. This is evidence that category membership
is genuinely graded, not just noisy Boolean. -/

-- ============================================================================
-- §20. Experiment 3: Nominal Choice (§5) — empirical findings
-- ============================================================================

/-! Exp 3 (§5.2) tests head-noun choice across taxonomic levels. Speakers
strongly prefer the subordinate term when it is needed for reference (β = 2.11,
SE = .17) and the basic level when both basic and superordinate suffice (β = .60,
SE = .15); higher object typicality → more subordinate mention (β = 4.82,
SE = 1.35); longer terms are dispreferred (length β = −.95, SE = .27) while word
frequency does not (β = .08, NS). The BDA (§5.3, Figure 19) prefers empirical
typicality over Boolean semantics (β_fixed → .004), fits high rationality
(β_i = 19.8), and — unlike the modifier model — a substantial length cost
(β_L = 2.69): nominal choice is NOT in the No-Brevity regime. These empirical
values are recorded in the module docstring; the model-side claim is the
structural nominal cs-RSA below (`φ_typ`, `nominal_overspec_preferred`,
`nominal_full_ordering`). Note the typicality sign flips between experiments —
Exp 2: typical → less *color* mention (an expected feature is uninformative);
Exp 3: typical → more *subordinate* mention (a better noun fit) — both consistent
with continuous semantics. -/

-- ============================================================================
-- §23. Nominal Reference Scene (basic-sufficient condition, §5)
-- ============================================================================

/-- Objects in a basic-sufficient reference game. The target is a dalmatian;
    the distractors are a cat and a bird. "Dog" uniquely identifies the
    target (basic-sufficient), so "dalmatian" is overspecific.

    This parallels the Exp 1 scene where "small" uniquely identifies the
    target and "small blue" is overmodified. -/
inductive NomWorld where
  /-- Target: a dalmatian -/
  | dalmatian
  /-- Distractor: a cat -/
  | cat
  /-- Distractor: a bird -/
  | bird
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Noun utterances at three taxonomic levels. -/
inductive NomUtterance where
  /-- Subordinate: "dalmatian" (overspecific in basic-sufficient) -/
  | sub
  /-- Basic: "dog" (SUFFICIENT to identify the target) -/
  | basic
  /-- Superordinate: "animal" (applies to all objects equally) -/
  | super
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §24. Typicality Meaning Function
-- ============================================================================

/-- Typicality-based meaning function φ_typ(u, o) ∈ [0,1].
    Each cell represents how typical object o is as an instance of
    the category named by utterance u.

    | Utterance | dalmatian | cat   | bird  |
    |-----------|-----------|-------|-------|
    | sub       | 19/20     | 1/100 | 1/100 |
    | basic     | 4/5       | 1/20  | 1/20  |
    | super     | 7/10      | 7/10  | 7/10  |

    Key structure: the dalmatian is a very typical dalmatian (19/20),
    a typical dog (4/5), and a moderately typical animal (7/10).
    The cat and bird have near-zero typicality for "dalmatian" and
    "dog" but are moderately typical animals.

    These values are illustrative, paralleling the §2 noise parameters
    for Exp 1. The paper's Exp 3 uses empirically elicited typicality
    ratings for 17 target items across three informativeness conditions. -/
def φ_typ : NomUtterance → NomWorld → ℚ
  | .sub, .dalmatian => 19/20
  | .sub, .cat => 1/100
  | .sub, .bird => 1/100
  | .basic, .dalmatian => 4/5
  | .basic, .cat => 1/20
  | .basic, .bird => 1/20
  | .super, .dalmatian => 7/10
  | .super, .cat => 7/10
  | .super, .bird => 7/10

/-- φ_typ is non-negative. -/
theorem φ_typ_nonneg (u : NomUtterance) (w : NomWorld) : 0 ≤ φ_typ u w := by
  cases u <;> cases w <;> simp [φ_typ] <;> norm_num

-- ============================================================================
-- §25. Nominal cs-RSA Config (α = 1, cost = 0)
-- ============================================================================

open RSA Real in
/-- cs-RSA model for nominal reference with typicality semantics.

    Same architecture as the Exp 1 modifier model — only the meaning
    function changes from noise-based to typicality-based. Cost = 0
    for the qualitative prediction; the paper's BDA finds β_L = 2.69
    (length cost is real for nouns but zero-cost suffices to demonstrate
    the overspecification prediction). -/
noncomputable def nominalCfg : RSAConfig NomUtterance NomWorld where
  meaning _ _ u w := ↑(φ_typ u w)
  meaning_nonneg _ _ u w := by exact_mod_cast φ_typ_nonneg u w
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
-- §26. Nominal L0 Verification
-- ============================================================================

/-- L0 posterior for the nominal scene (ℚ-valued). -/
def nomL0_q (u : NomUtterance) (w : NomWorld) : ℚ :=
  φ_typ u w / (φ_typ u .dalmatian + φ_typ u .cat + φ_typ u .bird)

/-- L0(dalmatian | "dalmatian") = 95/97 ≈ 0.979. Near-perfect
    identification — the subordinate term almost uniquely picks
    out the dalmatian via typicality. -/
theorem nomL0_sub_target : nomL0_q .sub .dalmatian = 95/97 := by
  norm_num [nomL0_q, φ_typ]

/-- L0(dalmatian | "dog") = 8/9 ≈ 0.889. Good identification —
    the basic-level term discriminates well because the distractors
    (cat, bird) are very atypical dogs. -/
theorem nomL0_basic_target : nomL0_q .basic .dalmatian = 8/9 := by
  norm_num [nomL0_q, φ_typ]

/-- L0(dalmatian | "animal") = 1/3. No discrimination — all three
    objects are equally typical animals. -/
theorem nomL0_super_target : nomL0_q .super .dalmatian = 1/3 := by
  norm_num [nomL0_q, φ_typ]

/-- The subordinate term sharpens L0 beyond the basic term:
    L0("dalmatian") > L0("dog"). Overspecific nouns carry real
    information through the typicality channel, just as redundant
    modifiers carry information through the noise channel. -/
theorem nomL0_overspec_sharpens :
    nomL0_q .sub .dalmatian > nomL0_q .basic .dalmatian := by
  norm_num [nomL0_q, φ_typ]

-- ============================================================================
-- §27. Core Prediction: Overspecification is Rational
-- ============================================================================

/-- **Nominal overspecification**: cs-RSA with typicality semantics
    predicts S1 prefers the subordinate "dalmatian" over the basic "dog"
    even when "dog" uniquely identifies the target.

    Mechanism: "dog" gives L0(target) = 8/9 (the dalmatian is typical
    but the distractors have nonzero dog-typicality). "Dalmatian" gives
    L0(target) = 95/97 ≈ 0.979 (near-perfect). The subordinate term
    carries more information through the typicality channel.

    This is the nominal analogue of `csrsa_overmod_preferred`:
    continuous semantics makes overspecification rational. -/
theorem nominal_overspec_preferred :
    nominalCfg.S1 () .dalmatian .sub > nominalCfg.S1 () .dalmatian .basic := by
  rsa_predict

/-- The basic term "dog" beats the superordinate "animal."
    "Dog" identifies the target well (L0 = 8/9), while "animal" does
    not discriminate at all (L0 = 1/3). -/
theorem nominal_basic_beats_super :
    nominalCfg.S1 () .dalmatian .basic > nominalCfg.S1 () .dalmatian .super := by
  rsa_predict

/-- Complete S1 ordering: sub > basic > super. Parallels the Exp 1
    ordering: overmod > sufficient > redundant. -/
theorem nominal_full_ordering :
    nominalCfg.S1 () .dalmatian .sub > nominalCfg.S1 () .dalmatian .basic ∧
    nominalCfg.S1 () .dalmatian .basic > nominalCfg.S1 () .dalmatian .super :=
  ⟨nominal_overspec_preferred, nominal_basic_beats_super⟩

-- ============================================================================
-- §28. Boolean Baseline: No Overspecification Preference
-- ============================================================================

/-- Boolean (crisp) typicality: {0, 1}. An object either belongs to
    the category or not, with no gradience.

    | Utterance | dalmatian | cat | bird |
    |-----------|-----------|-----|------|
    | sub       | 1         | 0   | 0    |
    | basic     | 1         | 0   | 0    |
    | super     | 1         | 1   | 1    |

    Key difference: Boolean L0(target | "dalmatian") = L0(target | "dog")
    = 1 (perfect identification). No overspecification preference. -/
def φ_typ_bool : NomUtterance → NomWorld → ℚ
  | .sub, .dalmatian => 1   | .sub, .cat => 0   | .sub, .bird => 0
  | .basic, .dalmatian => 1 | .basic, .cat => 0  | .basic, .bird => 0
  | .super, .dalmatian => 1 | .super, .cat => 1  | .super, .bird => 1

open RSA Real in
/-- Boolean RSA for nominal reference. Same architecture as the
    continuous model but with crisp {0,1} typicality. -/
noncomputable def nomBoolCfg : RSAConfig NomUtterance NomWorld where
  meaning _ _ u w := ↑(φ_typ_bool u w)
  meaning_nonneg _ _ u w := by cases u <;> cases w <;> simp [φ_typ_bool]
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

/-- Boolean RSA does NOT prefer overspecification: "dalmatian" is NOT
    better than "dog." Both give L0(target) = 1.0 (perfect identification),
    so the extra specificity provides zero information. -/
theorem nom_bool_no_overspec :
    ¬(nomBoolCfg.S1 () .dalmatian .sub > nomBoolCfg.S1 () .dalmatian .basic) := by
  rsa_predict

-- ============================================================================
-- §29. The Contrast: Typicality Makes the Difference
-- ============================================================================

/-- **The contrast**: typicality-based cs-RSA predicts overspecification
    where Boolean RSA does not. Typicality is to nouns what noise is to
    adjectives.

    | Prediction                | cs-RSA  | Boolean |
    |---------------------------|---------|---------|
    | Exp 1: overmod > suff     | ✓       | ✗       |
    | Exp 3: overspec > suff    | ✓       | ✗       |

    Both predictions follow from the same mechanism: continuous ∈ [0,1]
    meaning functions allow redundant/overspecific expressions to carry
    real information that Boolean {0,1} semantics cannot capture. -/
theorem typicality_makes_the_difference :
    -- cs-RSA with typicality: overspecification helps
    nominalCfg.S1 () .dalmatian .sub > nominalCfg.S1 () .dalmatian .basic ∧
    -- Boolean: overspecification doesn't help
    ¬(nomBoolCfg.S1 () .dalmatian .sub > nomBoolCfg.S1 () .dalmatian .basic) :=
  ⟨nominal_overspec_preferred, nom_bool_no_overspec⟩

-- ============================================================================
-- §30. Bridge: Overmod and Overspec Are the Same Mechanism
-- ============================================================================

/-- The unified mechanism: continuous semantics makes both overmodification
    (Exp 1) and overspecification (Exp 3) rational. Boolean semantics
    predicts neither.

    | Phenomenon     | Modifiers (Exp 1)      | Nouns (Exp 3)            |
    |----------------|------------------------|--------------------------|
    | Sufficient     | "small" (size)         | "dog" (basic level)      |
    | Overinformative| "small blue" (+ color) | "dalmatian" (sub level)  |
    | Continuous φ   | noise channels         | typicality ratings       |
    | cs-RSA         | overmod > sufficient   | overspec > sufficient    |
    | Boolean        | overmod = sufficient   | overspec = sufficient    |

    Both predictions are proved as theorems from the same RSA architecture
    with the same s1Score function — only the meaning function differs. -/
theorem unified_continuous_semantics :
    -- Exp 1: noise makes overmodification rational
    cfg.S1 () target .smallBlue > cfg.S1 () target .small ∧
    ¬(boolCfg.S1 () target .smallBlue > boolCfg.S1 () target .small) ∧
    -- Exp 3: typicality makes overspecification rational
    nominalCfg.S1 () .dalmatian .sub > nominalCfg.S1 () .dalmatian .basic ∧
    ¬(nomBoolCfg.S1 () .dalmatian .sub > nomBoolCfg.S1 () .dalmatian .basic) :=
  ⟨csrsa_overmod_preferred, bool_no_overmod_preference,
   nominal_overspec_preferred, nom_bool_no_overspec⟩

-- ============================================================================
-- §31. Cost-Parameterized Models
-- ============================================================================

/-! The informativity–brevity trade-off is central to the paper's
findings. We parameterize S1 with a cost weight c for both modifiers
(Exp 1) and nouns (Exp 3), then prove:

1. Both regimes (overinformative preferred, sufficient preferred) exist
2. The modifier model is more robust to cost than the nominal model
3. This differential robustness explains why β_c is unidentifiable for
   modifiers (wide HDI: [0, 0.26]) but identifiable for nouns (β_L = 2.69)

The key insight: noise-based modifier semantics produces a larger
informativity gap (L0 = 99/124 vs 2/3 = gap of ~0.13) than
typicality-based nominal semantics (L0 = 95/97 vs 8/9 = gap of ~0.09),
so modifiers can absorb more cost before the ordering flips. -/

-- ── Modifier cost model ─────────────────────────────────────────────────────

/-- Cost of modifier utterances. Two-word utterances (containing both
    size and color) cost 1; single-word utterances cost 0. -/
def modCost : Utterance → ℚ
  | .big | .small | .blue | .red => 0
  | .bigBlue | .bigRed | .smallBlue => 1

/-- S1 score for modifiers with cost discount c ≥ 0.
    S1(c, w, u) = L0(w|u) / (1 + c · cost(u)). -/
def S1_mod_cost (c : ℚ) (w : World) (u : Utterance) : ℚ :=
  L0_q u w / (1 + c * modCost u)

-- ── Nominal cost model ──────────────────────────────────────────────────────

/-- Relative utterance cost for nouns. Subordinate terms are longer
    than basic: "dalmatian" (9 chars) vs "dog" (3 chars). -/
def nomCost : NomUtterance → ℚ
  | .sub => 1     -- subordinate: longest
  | .basic => 0   -- basic: shortest (baseline)
  | .super => 1/2 -- superordinate: moderate

/-- S1 score for nouns with cost discount c ≥ 0.
    S1(c, w, u) = L0(w|u) / (1 + c · cost(u)). -/
def S1_nom_cost (c : ℚ) (w : NomWorld) (u : NomUtterance) : ℚ :=
  nomL0_q u w / (1 + c * nomCost u)

-- ── Existence: both regimes are realizable ──────────────────────────────────

/-- **Modifier existence**: both the overmod regime and the sufficient
    regime are realizable by varying cost. -/
theorem mod_cost_regime_existence :
    (∃ c : ℚ, 0 ≤ c ∧ S1_mod_cost c target .smallBlue > S1_mod_cost c target .small) ∧
    (∃ c : ℚ, 0 ≤ c ∧ S1_mod_cost c target .small > S1_mod_cost c target .smallBlue) :=
  ⟨⟨0, le_refl 0, by norm_num [S1_mod_cost, L0_q, φ, modCost, RSA.Noise.sizeMatch,
        RSA.Noise.sizeMismatch, RSA.Noise.colorMatch, RSA.Noise.colorMismatch]⟩,
   ⟨1/4, by norm_num, by norm_num [S1_mod_cost, L0_q, φ, modCost, RSA.Noise.sizeMatch,
        RSA.Noise.sizeMismatch, RSA.Noise.colorMatch, RSA.Noise.colorMismatch]⟩⟩

/-- **Nominal existence**: both the overspec regime and the basic-level
    regime are realizable by varying cost. -/
theorem nom_cost_regime_existence :
    (∃ c : ℚ, 0 ≤ c ∧ S1_nom_cost c .dalmatian .sub > S1_nom_cost c .dalmatian .basic) ∧
    (∃ c : ℚ, 0 ≤ c ∧ S1_nom_cost c .dalmatian .basic > S1_nom_cost c .dalmatian .sub) :=
  ⟨⟨0, le_refl 0, by norm_num [S1_nom_cost, nomL0_q, φ_typ, nomCost]⟩,
   ⟨1/5, by norm_num, by norm_num [S1_nom_cost, nomL0_q, φ_typ, nomCost]⟩⟩

-- ── Differential robustness ─────────────────────────────────────────────────

/-- At moderate cost c = 3/20, the modifier model STILL predicts
    overmodification but the nominal model ALREADY predicts basic level.

    The modifier prediction is more robust because the informativity gap
    from noise (L0 = 99/124 vs 2/3) is larger than the gap from
    typicality (L0 = 95/97 vs 8/9). Overmodification can absorb more
    cost before the ordering flips.

    This explains why the BDA finds:
    - β_c wide HDI [0, 0.26]: many cost values produce overmod → cost
      is unidentifiable
    - β_L = 2.69 (narrow HDI): the model is sensitive to cost → cost
      is identifiable -/
theorem differential_cost_robustness :
    -- Modifiers: overmod survives at c = 3/20
    S1_mod_cost (3/20) target .smallBlue > S1_mod_cost (3/20) target .small ∧
    -- Nouns: basic wins at c = 3/20
    S1_nom_cost (3/20) .dalmatian .basic > S1_nom_cost (3/20) .dalmatian .sub := by
  refine ⟨?_, ?_⟩
  · norm_num [S1_mod_cost, L0_q, φ, modCost, RSA.Noise.sizeMatch,
      RSA.Noise.sizeMismatch, RSA.Noise.colorMatch, RSA.Noise.colorMismatch]
  · norm_num [S1_nom_cost, nomL0_q, φ_typ, nomCost]

/-- The full crossover picture: both models transition from
    overinformative-preferred to sufficient-preferred, but at
    different cost levels.

    | Cost c | Modifiers          | Nouns              |
    |--------|--------------------|--------------------|
    | 0      | overmod > suff     | overspec > basic   |
    | 1/10   | overmod > suff     | overspec > basic   |
    | 3/20   | overmod > suff     | basic > overspec   |
    | 1/5    | suff > overmod     | basic > overspec   |
    | 1/4    | suff > overmod     | basic > overspec   |

    The nominal model crosses over between c = 1/10 and c = 3/20.
    The modifier model crosses over between c = 3/20 and c = 1/5. -/
theorem cost_crossover_table :
    -- c = 0: both prefer overinformative
    S1_mod_cost 0 target .smallBlue > S1_mod_cost 0 target .small ∧
    S1_nom_cost 0 .dalmatian .sub > S1_nom_cost 0 .dalmatian .basic ∧
    -- c = 1/10: both still prefer overinformative
    S1_mod_cost (1/10) target .smallBlue > S1_mod_cost (1/10) target .small ∧
    S1_nom_cost (1/10) .dalmatian .sub > S1_nom_cost (1/10) .dalmatian .basic ∧
    -- c = 3/20: modifiers still overmod, nouns flip to basic
    S1_mod_cost (3/20) target .smallBlue > S1_mod_cost (3/20) target .small ∧
    S1_nom_cost (3/20) .dalmatian .basic > S1_nom_cost (3/20) .dalmatian .sub ∧
    -- c = 1/5: both flip to sufficient
    S1_mod_cost (1/5) target .small > S1_mod_cost (1/5) target .smallBlue ∧
    S1_nom_cost (1/5) .dalmatian .basic > S1_nom_cost (1/5) .dalmatian .sub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [S1_mod_cost, S1_nom_cost, L0_q, nomL0_q, φ, φ_typ, modCost, nomCost,
      RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch, RSA.Noise.colorMatch,
      RSA.Noise.colorMismatch]

end DegenEtAl2020

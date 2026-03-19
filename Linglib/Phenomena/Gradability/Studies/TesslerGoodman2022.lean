import Linglib.Theories.Semantics.Degree.Core
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Phenomena.Gradability.ComparisonClass
import Linglib.Phenomena.Gradability.Studies.LassiterGoodman2017
import Linglib.Core.NestedRestriction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{tessler-goodman-2022}: Warm (for Winter)
@cite{tessler-goodman-2022} @cite{lassiter-goodman-2017}

Cognitive Science 46 (2022) e13095.

## Core Insight

Comparison class inference uses the SAME uncertain threshold mechanism as
adjective interpretation (@cite{lassiter-goodman-2017}). The listener jointly
infers the degree x AND the comparison class c (Eq. 1):

    L₁(x, c | u, k) ∝ S₁(u | x, c) · P(x | k) · P(c | k)

The comparison class c determines L0's height prior: subordinate uses the
kind's distribution (e.g., basketball players), superordinate uses the
general population (people). The threshold θ is marginalized analytically
following @cite{lassiter-goodman-2017}'s threshold RSA framework (the height priors are identical — see
`personWeight_eq_lassiterGoodman` and `basketballWeight_eq_lassiterGoodman`).

## Main Prediction: Polarity × Expectations Interaction

- "tall basketball player" → superordinate (people) comparison class
- "short basketball player" → subordinate (basketball players) comparison class
- Pattern reverses for jockeys (expected short)

The interaction emerges from RSA reasoning: a speaker saying "tall" about a
basketball player is more informative under superordinate comparison (the
L0 normalization Z_c(tall) differs by comparison class because the height
distribution shifts), so L1 infers superordinate. For "short," subordinate
comparison is more informative.

## Simplifications

- **α = 1** (the paper fits α₁ ≈ 1.45, α₂ ≈ 5.31; α=1 suffices for
  qualitative predictions since S₁ ∝ L₀^α is monotone in α)
- **No utterance costs** (Note 3: costs assumed equal for all utterances,
  so S₁(u | x, c) ∝ L₀(x | u, c)^α; cf. @cite{lassiter-goodman-2017}
  which has C(tall)=C(short)=2, C(∅)=0)
- **Flat comparison class prior** (P(c|k) uniform; the paper's "Flat prior"
  model variant from Table 2; the full model fits basic-level bias +
  frequency effects, but the flat prior already yields the qualitative
  polarity × expectations pattern)
- **Two extreme categories** (basketball=high, jockey=low; the paper uses
  three per item set including a medium control like soccer player/golfer
  where no polarity effect is predicted)

## Model Architecture

Per-kind RSAConfig with `Latent = ComparisonClass`, `World = Height`:
- `meaning(c, u, h)` = P(h | c) · |{θ : ⟦u⟧(h,θ)}|  (marginalized threshold)
- `worldPrior(h)` = P(h | k)  (L1's kind-specific height prior)
- `latentPrior(c)` = P(c | k)  (flat comparison class prior)

## Verified Predictions

### S1 Endorsement (speaker-level)

| # | Prediction | Kind | Height | Comp. Class | Theorem |
|---|-----------|------|--------|-------------|---------|
| 1 | "tall" endorsed | basketball | h=6 | super | `basketball_tall_endorsed_super` |
| 2 | "tall" NOT endorsed | basketball | h=6 | sub | `basketball_tall_not_endorsed_sub` |
| 3 | "short" endorsed | basketball | h=5 | sub | `basketball_short_endorsed_sub` |
| 4 | "short" NOT endorsed | basketball | h=5 | super | `basketball_short_not_endorsed_super` |
| 5 | "tall" endorsed | jockey | h=4 | sub | `jockey_tall_endorsed_sub` |
| 6 | "tall" NOT endorsed | jockey | h=4 | super | `jockey_tall_not_endorsed_super` |
| 7 | "short" endorsed | jockey | h=4 | super | `jockey_short_endorsed_super` |
| 8 | "short" NOT endorsed | jockey | h=4 | sub | `jockey_short_not_endorsed_sub` |

### L1 Comparison Class Inference (Eq. 1 — the paper's main prediction)

| # | Adj | Kind | Inferred CC | Theorem |
|---|-----|------|-------------|---------|
| 9 | tall | basketball | super | `basketball_tall_infers_super` |
| 10 | short | basketball | sub | `basketball_short_infers_sub` |
| 11 | tall | jockey | sub | `jockey_tall_infers_sub` |
| 12 | short | jockey | super | `jockey_short_infers_super` |

### Alternative Literal Listener (Eq. 6, Fig. 2 — opposite predictions)

| # | Kind | Adj | Literal | Pragmatic | Theorem |
|---|------|-----|---------|-----------|---------|
| 13 | basketball | tall | sub | super (#9) | `literal_basketball_tall_sub` |
| 14 | basketball | short | super | sub (#10) | `literal_basketball_short_super` |
| 15 | jockey | tall | super | sub (#11) | `literal_jockey_tall_super` |
| 16 | jockey | short | sub | super (#12) | `literal_jockey_short_sub` |
-/

set_option autoImplicit false

namespace Phenomena.Gradability.Studies.TesslerGoodman2022

open Core.Scale (Degree Threshold deg thr allDegrees allThresholds
  Degree.toNat Threshold.toNat)
open Semantics.Degree (positiveMeaning negativeMeaning)

-- ============================================================================
-- § 1. Domain Types
-- ============================================================================

/-- Discretized height: 0 through 10 in discrete steps (11 values). -/
abbrev Height := Degree 10

/-- Comparison classes: subordinate (the kind itself) or superordinate
    (the general population). -/
inductive ComparisonClass where
  | subordinate   -- compare to the specific kind (basketball players)
  | superordinate -- compare to the broader category (people)
  deriving Repr, DecidableEq, BEq, Fintype

/-- Kinds (nominals) that can be modified by adjectives. -/
inductive Kind where
  | person            -- generic person (baseline)
  | basketballPlayer  -- expected to be tall
  | jockey            -- expected to be short
  deriving Repr, DecidableEq, BEq, Fintype

/-- Utterances: positive adjective, negative adjective, or silence. -/
inductive Utterance where
  | tall    -- "x is tall"
  | short   -- "x is short"
  | silent  -- say nothing (null utterance)
  deriving Repr, DecidableEq, BEq, Fintype

-- ============================================================================
-- § 2. Height Priors (unnormalized weights)
-- ============================================================================

/-- Height weight for generic people: symmetric, peaked at h=5.
    Approximates a discretized normal centered at the population mean. -/
def personHeightWeight (h : Height) : Nat :=
  match h.toNat with
  | 0 => 1 | 1 => 2 | 2 => 5 | 3 => 10 | 4 => 15
  | 5 => 20 | 6 => 15 | 7 => 10 | 8 => 5 | 9 => 2 | _ => 1

/-- Height weight for basketball players: shifted right, peaked at h=7. -/
def basketballHeightWeight (h : Height) : Nat :=
  match h.toNat with
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 5
  | 5 => 10 | 6 => 15 | 7 => 20 | 8 => 15 | 9 => 10 | _ => 5

/-- Height weight for jockeys: shifted left, peaked at h=3. -/
def jockeyHeightWeight (h : Height) : Nat :=
  match h.toNat with
  | 0 => 5 | 1 => 10 | 2 => 15 | 3 => 20 | 4 => 15
  | 5 => 10 | 6 => 5 | 7 => 2 | 8 => 1 | 9 => 0 | _ => 0

/-- Height weight for a given kind: P(h | k) (unnormalized). -/
def heightWeight (k : Kind) : Height → Nat :=
  match k with
  | .person => personHeightWeight
  | .basketballPlayer => basketballHeightWeight
  | .jockey => jockeyHeightWeight

/-- L0's height weight conditioned on comparison class.
    Subordinate uses the kind's own distribution; superordinate uses people. -/
def l0HeightWeight (c : ComparisonClass) (k : Kind) : Height → Nat :=
  match c with
  | .subordinate => heightWeight k
  | .superordinate => personHeightWeight

/-- Comparison class prior weights: P(c | k) (unnormalized).
    Flat prior: subordinate and superordinate equally likely a priori.
    The qualitative polarity × expectations interaction emerges entirely
    from pragmatic reasoning about informativity, not from prior bias.
    (Paper Table 2: "Flat prior" model variant, r² = 0.136 for CC inference.) -/
def compClassWeight (_k : Kind) : ComparisonClass → Nat :=
  λ _ => 1

-- ============================================================================
-- § 3. Semantics: Threshold-Marginalized Meaning
-- ============================================================================

/-- Number of thresholds θ ∈ {0,...,9} satisfying ⟦u⟧(h,θ) = true.

    For tall (`positiveMeaning`): |{θ : h > θ}| = h.toNat
    For short (`negativeMeaning`): |{θ : h < θ}| = 9 - h.toNat
    For silent: 10 (all thresholds pass) -/
def thresholdCount (u : Utterance) (h : Height) : Nat :=
  match u with
  | .tall => h.toNat
  | .short => 9 - h.toNat  -- Nat subtraction floors at 0
  | .silent => 10

/-- Grounding: `thresholdCount .tall` equals the count of thresholds
    satisfying `positiveMeaning`. -/
theorem thresholdCount_tall_eq_card :
    ∀ h : Height, thresholdCount .tall h =
      (Finset.univ.filter (λ θ : Threshold 10 => positiveMeaning h θ)).card := by
  native_decide

/-- Grounding: `thresholdCount .short` equals the count of thresholds
    satisfying `negativeMeaning`. -/
theorem thresholdCount_short_eq_card :
    ∀ h : Height, thresholdCount .short h =
      (Finset.univ.filter (λ θ : Threshold 10 => negativeMeaning h θ)).card := by
  native_decide

-- ============================================================================
-- § 4. RSAConfig — Comparison Class Inference Model
-- ============================================================================

open Real (rpow rpow_nonneg)

/-- RSAConfig for comparison class inference, parameterized by kind k.

    Extends @cite{lassiter-goodman-2017}'s threshold RSA: instead of treating
    the threshold θ as a latent (as LG2017 does), θ is marginalized analytically
    into `thresholdCount`, and the comparison class c becomes the latent variable.

    - `meaning(c, u, h)` = P(h | c) · thresholdCount(u, h)
    - `worldPrior(h)` = P(h | k)
    - `latentPrior(c)` = P(c | k) = 1 (flat prior)
    - **α = 1**, **no utterance costs** (Note 3: costs equal ⇒ S₁ ∝ L₀^α)

    S1's scores depend on c through L0's normalization constant Z_c(u),
    which shifts with the comparison class height distribution. -/
@[reducible]
noncomputable def mkCompClassCfg (k : Kind) : RSA.RSAConfig Utterance Height where
  Latent := ComparisonClass
  meaning _ c u h := (l0HeightWeight c k h : ℝ) * (thresholdCount u h : ℝ)
  meaning_nonneg _ _ _ _ := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  worldPrior h := (heightWeight k h : ℝ)
  worldPrior_nonneg _ := Nat.cast_nonneg _
  latentPrior _ c := (compClassWeight k c : ℝ)
  latentPrior_nonneg _ _ := Nat.cast_nonneg _

/-- Basketball player config: height distribution shifted right (peak at h=7). -/
@[reducible]
noncomputable def basketballCfg : RSA.RSAConfig Utterance Height :=
  mkCompClassCfg .basketballPlayer

/-- Jockey config: height distribution shifted left (peak at h=3). -/
@[reducible]
noncomputable def jockeyCfg : RSA.RSAConfig Utterance Height :=
  mkCompClassCfg .jockey

-- ============================================================================
-- § 5. Semantic Properties
-- ============================================================================

/-- Basketball players' weighted height sum exceeds the person mean:
    Σ P(h|bball)·h = 568 > 430 = Σ P(h|person)·h (unnormalized). -/
theorem basketball_expected_taller_than_person :
    (Finset.univ.sum λ h : Height => basketballHeightWeight h * h.toNat) >
    (Finset.univ.sum λ h : Height => personHeightWeight h * h.toNat) := by native_decide

/-- Jockeys' weighted height sum is below the person mean. -/
theorem jockey_expected_shorter_than_person :
    (Finset.univ.sum λ h : Height => jockeyHeightWeight h * h.toNat) <
    (Finset.univ.sum λ h : Height => personHeightWeight h * h.toNat) := by native_decide

/-- For person, subordinate and superordinate use the same height distribution,
    so comparison class makes no difference. -/
theorem person_classes_identical :
    ∀ h : Height, l0HeightWeight .subordinate .person h =
                  l0HeightWeight .superordinate .person h := by
  native_decide

/-- Sanity check: silence doesn't discriminate between comparison classes.

    For the person kind (where subordinate = superordinate by
    `person_classes_identical`), L1 hearing silence assigns equal
    posterior to both comparison classes. This confirms the model's
    baseline: only informative utterances (tall/short) shift CC inference. -/
noncomputable def personCfg : RSA.RSAConfig Utterance Height :=
  mkCompClassCfg .person

theorem silent_no_cc_preference :
    personCfg.L1_latent .silent .subordinate =
    personCfg.L1_latent .silent .superordinate := by rsa_predict

-- ============================================================================
-- § 6. S1 Endorsement Predictions — Polarity × Expectations Interaction
-- ============================================================================

/-! ### Basketball Player (expected tall)

At height 6 (above person mean 5, below basketball mean ~6.8):
- Under superordinate (people): "tall" IS endorsed (h=6 > E[person]=5)
- Under subordinate (basketball): "tall" NOT endorsed (h=6 < E[basketball]≈6.8)

At height 5 (at person mean, well below basketball mean):
- Under subordinate (basketball): "short" IS endorsed
- Under superordinate (people): "short" NOT endorsed (h=5 ≈ E[person]=5) -/

/-- "Tall" endorsed under superordinate at h=6: a basketball player of height 6
    is tall for a person (6 > person mean = 5). -/
theorem basketball_tall_endorsed_super :
    basketballCfg.S1 .superordinate (deg 6) .tall >
    basketballCfg.S1 .superordinate (deg 6) .silent := by
  rsa_predict

/-- "Tall" NOT endorsed under subordinate at h=6: a basketball player of
    height 6 is average for a basketball player (6 < basketball mean ≈ 6.8). -/
theorem basketball_tall_not_endorsed_sub :
    ¬(basketballCfg.S1 .subordinate (deg 6) .tall >
      basketballCfg.S1 .subordinate (deg 6) .silent) := by
  rsa_predict

/-- "Short" endorsed under subordinate at h=5: height 5 is well below the
    basketball mean, so "short" is informative within basketball players. -/
theorem basketball_short_endorsed_sub :
    basketballCfg.S1 .subordinate (deg 5) .short >
    basketballCfg.S1 .subordinate (deg 5) .silent := by
  rsa_predict

/-- "Short" NOT endorsed under superordinate at h=5: height 5 is exactly
    the person mean, so "short" is uninformative relative to people. -/
theorem basketball_short_not_endorsed_super :
    ¬(basketballCfg.S1 .superordinate (deg 5) .short >
      basketballCfg.S1 .superordinate (deg 5) .silent) := by
  rsa_predict

/-! ### Jockey (expected short)

At height 4 (below person mean 5, above jockey mean ~3.2):
- Under subordinate (jockeys): "tall" IS endorsed (h=4 > E[jockey]≈3.2)
- Under superordinate (people): "tall" NOT endorsed (h=4 < E[person]=5)
- Under superordinate (people): "short" IS endorsed (h=4 < E[person]=5)
- Under subordinate (jockeys): "short" NOT endorsed (h=4 > E[jockey]≈3.2) -/

/-- "Tall" endorsed under subordinate at h=4: a jockey of height 4
    is tall for a jockey (4 > jockey mean ≈ 3.2). -/
theorem jockey_tall_endorsed_sub :
    jockeyCfg.S1 .subordinate (deg 4) .tall >
    jockeyCfg.S1 .subordinate (deg 4) .silent := by
  rsa_predict

/-- "Tall" NOT endorsed under superordinate at h=4: height 4 is below the
    person mean, so "tall" is uninformative relative to people. -/
theorem jockey_tall_not_endorsed_super :
    ¬(jockeyCfg.S1 .superordinate (deg 4) .tall >
      jockeyCfg.S1 .superordinate (deg 4) .silent) := by
  rsa_predict

/-- "Short" endorsed under superordinate at h=4: height 4 is below the
    person mean (4 < E[person]=5). -/
theorem jockey_short_endorsed_super :
    jockeyCfg.S1 .superordinate (deg 4) .short >
    jockeyCfg.S1 .superordinate (deg 4) .silent := by
  rsa_predict

/-- "Short" NOT endorsed under subordinate at h=4: a jockey of height 4
    is average for a jockey, so "short" is uninformative. -/
theorem jockey_short_not_endorsed_sub :
    ¬(jockeyCfg.S1 .subordinate (deg 4) .short >
      jockeyCfg.S1 .subordinate (deg 4) .silent) := by
  rsa_predict

-- ============================================================================
-- § 7. Cross-Study Bridge: @cite{lassiter-goodman-2017}
-- ============================================================================

/-! This model extends @cite{lassiter-goodman-2017}'s threshold RSA.
The key structural relationship:
- LG2017 treats the threshold θ as a `Latent` variable (L1 infers θ)
- TG2022 marginalizes θ analytically (via `thresholdCount`) and adds
  comparison class c as the `Latent` variable (L1 infers c)

The height priors are identical — this is the same empirical domain,
with a different question being asked of the same RSA machinery. -/

open RSA.LassiterGoodman2017 in
/-- Person height weights match @cite{lassiter-goodman-2017}'s general
    population prior (same bell curve peaked at h=5). -/
theorem personWeight_eq_lassiterGoodman :
    ∀ h : Height, (personHeightWeight h : ℚ) =
      RSA.LassiterGoodman2017.heightPrior h := by native_decide

open RSA.LassiterGoodman2017 in
/-- Basketball height weights match @cite{lassiter-goodman-2017}'s
    basketball player prior (same bell curve peaked at h=7). -/
theorem basketballWeight_eq_lassiterGoodman :
    ∀ h : Height, (basketballHeightWeight h : ℚ) =
      RSA.LassiterGoodman2017.basketballPrior h := by native_decide

-- ============================================================================
-- § 8. L1 Comparison Class Inference (Eq. 1)
-- ============================================================================

/-! ### The paper's main prediction: L1 comparison class inference

The S1 endorsement theorems (§ 6) show that S1 behaves differently under
each comparison class. The paper's Eq. 1 prediction is about the LISTENER:
after hearing an adjective about a kind, which comparison class does L1 infer?

    L₁(x, c | u, k) ∝ S₁(u | x, c) · P(x | k) · P(c | k)

After marginalizing over height x, the posterior over comparison classes is
`RSAConfig.L1_latent`. The polarity × expectations interaction:

- **Expected adjective** (tall basketball, short jockey) → **superordinate**
- **Unexpected adjective** (short basketball, tall jockey) → **subordinate** -/

/-- Basketball + "tall" → listener infers superordinate: a basketball player
    described as "tall" is tall even for a person — unexpected, hence
    informative under the superordinate comparison class. -/
theorem basketball_tall_infers_super :
    basketballCfg.L1_latent .tall .superordinate >
    basketballCfg.L1_latent .tall .subordinate := by rsa_predict

/-- Basketball + "short" → listener infers subordinate: "short for a
    basketball player" is more informative than "short for a person"
    (since basketball players are expected to be tall). -/
theorem basketball_short_infers_sub :
    basketballCfg.L1_latent .short .subordinate >
    basketballCfg.L1_latent .short .superordinate := by rsa_predict

/-- Jockey + "tall" → listener infers subordinate: "tall for a jockey"
    is more informative than "tall for a person" (since jockeys are
    expected to be short). -/
theorem jockey_tall_infers_sub :
    jockeyCfg.L1_latent .tall .subordinate >
    jockeyCfg.L1_latent .tall .superordinate := by rsa_predict

/-- Jockey + "short" → listener infers superordinate: a jockey described
    as "short" is short even for a person — unexpected, hence informative
    under the superordinate comparison class. -/
theorem jockey_short_infers_super :
    jockeyCfg.L1_latent .short .superordinate >
    jockeyCfg.L1_latent .short .subordinate := by rsa_predict

-- ============================================================================
-- § 9. Connection to Comparison Class Data
-- ============================================================================

/-! The polarity × expectations interaction from §§ 6, 8 matches the empirical
patterns in `Phenomena.Gradability.ComparisonClass`:

| Data pattern | L1 inference | S1 endorsed | S1 not endorsed |
|-------------|-------------|-------------|-----------------|
| `tallBasketball` → super | `basketball_tall_infers_super` | `basketball_tall_endorsed_super` | `basketball_tall_not_endorsed_sub` |
| `shortBasketball` → sub | `basketball_short_infers_sub` | `basketball_short_endorsed_sub` | `basketball_short_not_endorsed_super` |
| `tallJockey` → sub | `jockey_tall_infers_sub` | `jockey_tall_endorsed_sub` | `jockey_tall_not_endorsed_super` |
| `shortJockey` → super | `jockey_short_infers_super` | `jockey_short_endorsed_super` | `jockey_short_not_endorsed_sub` |

In every case, the EXPECTED adjective (consistent with the kind's height
distribution) triggers SUPERORDINATE comparison, and the UNEXPECTED adjective
triggers SUBORDINATE comparison. The L1 inference theorems (§ 8) directly
replicate the paper's Eq. 1 prediction. -/

open Phenomena.Gradability.ComparisonClass in
/-- The data records the polarity × expectations pattern. -/
theorem polarity_expectations_confirmed :
    tallBasketball.inferredClass = "superordinate" ∧
    shortBasketball.inferredClass = "subordinate" ∧
    tallJockey.inferredClass = "subordinate" ∧
    shortJockey.inferredClass = "superordinate" := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10. Alternative: Literal Listener Model (Eq. 6, Fig. 2)
-- ============================================================================

/-! ### The literal model makes the OPPOSITE predictions

@cite{tessler-goodman-2022} §2 contrasts the pragmatic listener (Eq. 1) with
an alternative literal listener (Eq. 6) that does not reason about a rational
speaker:

    L₀(x, θ, c | u, k) ∝ δ_{⟦u⟧}(x,θ) · P(x | c) · P(θ) · P(c | k)

This model updates beliefs about x and c jointly via the literal meaning,
using the comparison-class-specific prior P(x | c), but without S1
informativity. It effectively asks: under which comparison class is the
utterance more likely to be literally true? For "tall basketball player,"
tallness is more probable under the basketball distribution (shifted right),
so the literal model prefers subordinate — the OPPOSITE of the pragmatic
model and the data.

The pragmatic model inverts this because S1 normalizes by the total
literal-listener mass Z_c(u), penalizing classes where the utterance is
uninformative (too many heights satisfy it) and rewarding classes where the
utterance is surprising. -/

/-- Unnormalized literal score: Σ_h P(h|c) · |{θ : ⟦u⟧(h,θ)}|.
    Total literal-listener mass for comparison class c, marginalized
    over heights and thresholds. -/
def literalClassScore (k : Kind) (c : ComparisonClass) (u : Utterance) : Nat :=
  Finset.univ.sum λ h : Height => l0HeightWeight c k h * thresholdCount u h

/-- Literal: basketball + "tall" → subordinate.
    Basketball players' rightward-shifted heights make "tall" more often
    literally true under subordinate comparison.
    Opposite of pragmatic `basketball_tall_infers_super`. -/
theorem literal_basketball_tall_sub :
    literalClassScore .basketballPlayer .subordinate .tall >
    literalClassScore .basketballPlayer .superordinate .tall := by native_decide

/-- Literal: basketball + "short" → superordinate.
    Opposite of pragmatic `basketball_short_infers_sub`. -/
theorem literal_basketball_short_super :
    literalClassScore .basketballPlayer .superordinate .short >
    literalClassScore .basketballPlayer .subordinate .short := by native_decide

/-- Literal: jockey + "tall" → superordinate.
    Opposite of pragmatic `jockey_tall_infers_sub`. -/
theorem literal_jockey_tall_super :
    literalClassScore .jockey .superordinate .tall >
    literalClassScore .jockey .subordinate .tall := by native_decide

/-- Literal: jockey + "short" → subordinate.
    Opposite of pragmatic `jockey_short_infers_super`. -/
theorem literal_jockey_short_sub :
    literalClassScore .jockey .subordinate .short >
    literalClassScore .jockey .superordinate .short := by native_decide

/-- Every literal prediction is reversed by the pragmatic model (Fig. 2).
    This is the paper's key scientific claim: comparison class inference
    requires social reasoning via S1, not just Bayesian updating on
    literal truth conditions. -/
theorem pragmatic_reverses_literal :
    basketballCfg.L1_latent .tall .superordinate >
    basketballCfg.L1_latent .tall .subordinate ∧
    basketballCfg.L1_latent .short .subordinate >
    basketballCfg.L1_latent .short .superordinate ∧
    jockeyCfg.L1_latent .tall .subordinate >
    jockeyCfg.L1_latent .tall .superordinate ∧
    jockeyCfg.L1_latent .short .superordinate >
    jockeyCfg.L1_latent .short .subordinate :=
  ⟨basketball_tall_infers_super, basketball_short_infers_sub,
   jockey_tall_infers_sub, jockey_short_infers_super⟩

-- ============================================================================
-- § 11. Dimension Generality: "Warm (for Winter)"
-- ============================================================================

/-! The paper's title example uses temperature, not height. The model is
dimension-general: any relative gradable adjective whose comparison class
shifts the degree prior produces the polarity × expectations interaction.

The temperature domain maps onto the height domain:
- Winter (expected cold) ↔ Jockey (expected short): prior peaked at 3
- Summer (expected warm) ↔ Basketball (expected tall): prior peaked at 7
- warm ↔ tall (positive adjective), cold ↔ short (negative adjective)

Since the weight functions are identical, the § 8 predictions transfer:

| Context | Adjective | Inferred CC | Height analogue |
|---------|-----------|-------------|-----------------|
| winter  | warm  | subordinate   | `jockey_tall_infers_sub` |
| winter  | cold  | superordinate | `jockey_short_infers_super` |
| summer  | warm  | superordinate | `basketball_tall_infers_super` |
| summer  | cold  | subordinate   | `basketball_short_infers_sub` |

This connects to `Core.Dimension.temperature`: a `sensory` domain with
`requiresComparisonClass = true` (@cite{sedivy-etal-1999}). -/

/-- Temperature is a comparison-class-sensitive dimension. -/
theorem temperature_requires_cc :
    Core.PropertyDomain.requiresComparisonClass .sensory = true := rfl

/-- The literal/pragmatic reversal transfers to temperature via the
    winter ↔ jockey mapping. The literal model predicts "warm in winter"
    → superordinate (warm is more often literally true in the general
    population than in winter), but the pragmatic model correctly predicts
    subordinate: "warm for winter" is informative within the season. -/
theorem literal_reversal_transfers_to_temp :
    -- Literal: "winter + warm" ↔ "jockey + tall" → superordinate
    literalClassScore .jockey .superordinate .tall >
    literalClassScore .jockey .subordinate .tall ∧
    -- Pragmatic: "winter + warm" ↔ "jockey + tall" → subordinate
    jockeyCfg.L1_latent .tall .subordinate >
    jockeyCfg.L1_latent .tall .superordinate :=
  ⟨literal_jockey_tall_super, jockey_tall_infers_sub⟩

-- ============================================================================
-- § 12. Connection to Generic Language (@cite{tessler-goodman-2019})
-- ============================================================================

/-! Threshold semantics for gradable adjectives generalizes to generic
language: "Birds fly south in the winter" ≈ P(x flies south | x is a bird) > θ
(@cite{tessler-goodman-2019}). Both models share:

1. A threshold variable θ setting the standard
2. A prior P(x | c) conditioned on category membership
3. Pragmatic inference about the contextually appropriate threshold/class

The comparison class model (this file) infers which c maximizes the pragmatic
listener's posterior. The generics model infers which θ is pragmatically
optimal. Same RSA machinery applied to different latent variables. -/

-- ============================================================================
-- § 13. Comparison Class as NestedRestriction
-- ============================================================================

/-! The comparison class hierarchy is structurally a `NestedRestriction`:
subordinate (restricted) ⊆ superordinate (unrestricted). Going from subordinate
to superordinate widens the reference population.

This connects comparison class inference to the same nesting pattern used
by @cite{ritchie-schiller-2024}'s domain restriction possibilities. -/

private def ComparisonClass.toFin : ComparisonClass → Fin 2
  | .subordinate => 0
  | .superordinate => 1

private theorem ComparisonClass.toFin_injective :
    Function.Injective ComparisonClass.toFin := by
  intro a b h; cases a <;> cases b <;> simp_all [ComparisonClass.toFin]

instance : LinearOrder ComparisonClass :=
  LinearOrder.lift' ComparisonClass.toFin ComparisonClass.toFin_injective

instance : OrderTop ComparisonClass where
  top := .superordinate
  le_top a := by cases a <;> decide

/-- Whether a height has nonzero prior weight for a given kind. -/
def isTypical (k : Kind) (h : Height) : Bool :=
  heightWeight k h > 0

/-- The comparison class hierarchy as a nested restriction on heights. -/
def compClassRestriction (k : Kind) : Core.NestedRestriction ComparisonClass Height where
  region
    | .subordinate => isTypical k
    | .superordinate => λ _ => true
  monotone {s₁ s₂} h d hr := by
    cases s₁ <;> cases s₂ <;> simp_all
    · exact absurd h (by decide)
  top_total _ := rfl

/-- Nesting: subordinate ⊆ superordinate for all kinds. -/
theorem compClass_nesting (k : Kind) (h : Height) :
    (compClassRestriction k).region .subordinate h = true →
    (compClassRestriction k).region .superordinate h = true :=
  (compClassRestriction k).subset_of_le (by decide) h

/-- Bridge to `Core.TwoLevel`: the study-local `ComparisonClass` is
    isomorphic to the generic two-level nesting type. -/
def ComparisonClass.toTwoLevel : ComparisonClass → Core.TwoLevel
  | .subordinate => .restricted
  | .superordinate => .full

/-- The isomorphism preserves order. -/
theorem ComparisonClass.toTwoLevel_monotone {a b : ComparisonClass}
    (h : a ≤ b) : a.toTwoLevel ≤ b.toTwoLevel := by
  revert h; cases a <;> cases b <;> decide

end Phenomena.Gradability.Studies.TesslerGoodman2022

import Linglib.Core.Scales.Scale
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod

/-!
# @cite{lassiter-goodman-2017}

Adjectival vagueness in a Bayesian model of interpretation.
Synthese 194:3801–3836.

## Innovation

Standard RSA models fix the literal meaning of each utterance. Threshold RSA
introduces a free semantic variable — the threshold θ — that the pragmatic
listener L1 jointly infers alongside the world state:

  P_L1(s, θ | u) ∝ P_S1(u | s, θ) · P(s) · P(θ)

This yields three key predictions (§4.3–4.4):
1. **Information transmission**: hearing "tall"/"short" shifts the height
   posterior above/below the prior mean despite vague semantics
2. **Pragmatic sweet spot**: the threshold posterior peaks at an intermediate
   value, not at extremes — low θ makes "tall" uninformative (high cost,
   low information gain); high θ makes it implausible
3. **Context sensitivity**: shifting the reference class prior (e.g., from
   the general population to basketball players) shifts both the height
   and threshold posteriors (§4.4, Figure 7)

## Semantics (§4.1)

Scalar adjectives have a free threshold variable (Eqs. 22–23):
- ⟦tall⟧(θ)(x) = 1 iff height(x) > θ  (Eq. 22)
- ⟦short⟧(θ)(x) = 1 iff height(x) < θ  (Eq. 23)

## RSAConfig Mapping

- **U** = `Utterance` (tall, short, silent)
- **W** = `Height` (Degree 10, 11 values: h0–h10)
- **Latent** = `Threshold` (Threshold 10, 10 values: θ0–θ9)
- **meaning(θ, u, h)** = `prior(h)` if ⟦u⟧_θ(h), else 0
  (§4.2: L0 includes the world prior)
- **s1Score** = `exp(α · (log L0(h|u,θ) − C(u)))` (§4.2)
- **worldPrior(h)** = `prior(h)`
- **latentPrior** = uniform (§4.2: "P(V) is thus uniform")
- **α** = 4 (§4.4)
- **C(tall) = C(short) = 2** (§4.4: C(u) = 2/3 × |u| in words,
  |"Sam is tall"| = 3), **C(∅) = 0**

The prior enters at both L0 (baked into `meaning`) and L1 (`worldPrior`),
matching §4.2 where P_{L0}(s) = P_{L1}(s).

## Verified Predictions

1. Hearing "tall" shifts height posterior upward (§4.4, Figure 5)
2. Hearing "short" shifts height posterior downward (§4.4, Figure 6)
3. Threshold posterior peaks at intermediate θ given "tall" (§4.4)
4. Basketball prior shifts L1("tall") toward taller heights (§4.4, Figure 7)
-/

namespace RSA.LassiterGoodman2017

open Core.Scale (Degree Threshold Degree.toNat Threshold.toNat
  deg thr allDegrees allThresholds)

-- ============================================================================
-- Domain: Heights and Thresholds
-- ============================================================================

/-- Discretized height values (h0–h10).

    The paper uses a continuous normal distribution over heights; we discretize
    to 11 values (Degree 10). -/
abbrev Height := Degree 10

/-- Threshold values (θ0–θ9).

    The threshold θ determines the cutoff: x is tall iff height(x) > θ
    (Eq. 21). -/
instance : NeZero (10 : Nat) := ⟨by omega⟩
abbrev Threshold := Core.Scale.Threshold 10

-- ============================================================================
-- Utterances
-- ============================================================================

/-- The speaker can say "tall," "short," or stay silent. -/
inductive Utterance where
  | tall    -- "Sam is tall"
  | short   -- "Sam is short"
  | silent  -- null utterance ∅
  deriving Repr, DecidableEq, Fintype

-- ============================================================================
-- Semantics (§4.1, Eqs. 22–23)
-- ============================================================================

open Semantics.Degree (positiveMeaning negativeMeaning)

/-- ⟦tall⟧(θ)(x) = 1 iff height(x) > θ (@cite{kennedy-2007}, positive form). -/
def tallMeaning (θ : Threshold) (h : Height) : Bool :=
  positiveMeaning h θ

/-- ⟦short⟧(θ)(x) = 1 iff height(x) < θ (@cite{kennedy-2007}, negative form). -/
def shortMeaning (θ : Threshold) (h : Height) : Bool :=
  negativeMeaning h θ

/-- Full meaning function: utterance × threshold → height → Bool.
    Silent is vacuously true (compatible with all heights). -/
def meaning (u : Utterance) (θ : Threshold) (h : Height) : Bool :=
  match u with
  | .tall => positiveMeaning h θ
  | .short => negativeMeaning h θ
  | .silent => true

-- ============================================================================
-- Priors (Section 4.2)
-- ============================================================================

/-- Height prior: discretized normal distribution centered at h5.

    The paper assumes a continuous normal P(s) over heights. We approximate
    with unnormalized weights [1,2,5,10,15,20,15,10,5,2,1] peaked at h5. -/
def heightPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 1    -- tails
  | 1 => 2
  | 2 => 5
  | 3 => 10
  | 4 => 15
  | 5 => 20   -- peak (mean)
  | 6 => 15
  | 7 => 10
  | 8 => 5
  | 9 => 2
  | _ => 1    -- tails

/-- Threshold prior: uniform over all thresholds (Section 4.2).

    "P(V) is thus uniform for all possible combinations of values
    for the elements of V." -/
def thresholdPrior : Threshold → ℚ := fun _ => 1

/-- Basketball player height prior: peak shifted to h7 (§4.4, Figure 7).

    The paper uses "two input priors with different means" to demonstrate
    context sensitivity. We shift the same bell shape rightward by 2 steps,
    truncating the left tail at zero. -/
def basketballPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 5
  | 5 => 10
  | 6 => 15
  | 7 => 20   -- peak shifted to h7
  | 8 => 15
  | 9 => 10
  | _ => 5

-- ============================================================================
-- Utterance Costs (§3; §4.4)
-- ============================================================================

/-- Utterance cost function.

    C(u) = 2/3 × length(u) in words.
    C("Sam is tall") = C("Sam is short") = 2/3 × 3 = 2.
    C(∅) = 0 (null utterance is free). -/
def utteranceCost (costWord : ℚ) : Utterance → ℚ
  | .tall => costWord
  | .short => costWord
  | .silent => 0

/-- Fitted cost value from Section 4.4: C = 2/3 × 3 = 2 for content words. -/
def paperCost : ℚ := 2

-- ============================================================================
-- RSAConfig (§4.2)
-- ============================================================================

open Real (rpow rpow_nonneg exp log exp_pos)

/-- Height prior as ℝ. -/
noncomputable def heightPriorR (h : Height) : ℝ := heightPrior h

theorem heightPriorR_nonneg : ∀ h : Height, 0 ≤ heightPriorR h := by
  intro h; simp only [heightPriorR]
  exact_mod_cast (by
    unfold heightPrior
    split <;> norm_num : (0 : ℚ) ≤ heightPrior h)

/-- Basketball height prior as ℝ. -/
noncomputable def basketballPriorR (h : Height) : ℝ := basketballPrior h

theorem basketballPriorR_nonneg : ∀ h : Height, 0 ≤ basketballPriorR h := by
  intro h; simp only [basketballPriorR]
  exact_mod_cast (by
    unfold basketballPrior
    split <;> norm_num : (0 : ℚ) ≤ basketballPrior h)

/-- Utterance cost as ℝ. -/
noncomputable def utteranceCostR (u : Utterance) : ℝ := utteranceCost paperCost u

/-- S1 belief-based score with utterance costs (Eq. 28):

    S1(u|s,V) ∝ exp(α · (log P_{L0}(s|u,V) − C(u)))

    Gated on `l0 u w = 0` because Lean's `log 0 = 0`, which would make
    `exp(α · (0 − C))` positive for false utterances. -/
noncomputable def beliefScore :
    (Utterance → Height → ℝ) → ℝ → Threshold → Height → Utterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - utteranceCostR u))

theorem beliefScore_nonneg :
    ∀ (l0 : Utterance → Height → ℝ) (α : ℝ) (l : Threshold) (w : Height) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ beliefScore l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [beliefScore]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

/-- Parametric RSAConfig for threshold models.

    Decouples the reference class prior from model structure so that
    `defaultCfg` and `basketballCfg` share the same architecture.

    Both L0 and L1 use the same prior (§4.2):
    - L0: P_{L0}(s|u,V) ∝ P(s) · ⟦u⟧_V(s)
    - L1: P_{L1}(s,V|u) ∝ P_{S1}(u|s,V) · P(s) · P(V)

    α = 4 (§4.4). -/
@[reducible]
noncomputable def mkThresholdCfg
    (prior : Height → ℝ) (hp : ∀ h, 0 ≤ prior h) :
    RSA.RSAConfig Utterance Height where
  Latent := Threshold
  meaning _ θ u h := if meaning u θ h then prior h else 0
  meaning_nonneg _ θ u h := by split <;> [exact hp h; exact le_refl 0]
  s1Score := beliefScore
  s1Score_nonneg := beliefScore_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior := prior
  worldPrior_nonneg := hp
  latentPrior_nonneg _ _ := by positivity

/-- Default config: general population prior (peak at h5). -/
@[reducible]
noncomputable def defaultCfg : RSA.RSAConfig Utterance Height :=
  mkThresholdCfg heightPriorR heightPriorR_nonneg

/-- Basketball config: basketball player prior (peak at h7).
    Tests context sensitivity (§4.4, Figure 7). -/
@[reducible]
noncomputable def basketballCfg : RSA.RSAConfig Utterance Height :=
  mkThresholdCfg basketballPriorR basketballPriorR_nonneg

-- ============================================================================
-- L1 Height Inference (Section 4.3, Figure 5)
-- ============================================================================

/-! ### Hearing "tall" shifts height posterior upward

The pragmatic listener L1, upon hearing "tall," infers that the speaker's
height is above average. The prior peaks at h5; L1("tall") shifts
probability mass toward higher heights (Figure 5, left panel). -/

theorem tall_shifts_upward :
    defaultCfg.L1 .tall (deg 8) > defaultCfg.L1 .tall (deg 2) := by
  rsa_predict

theorem tall_shifts_upward' :
    defaultCfg.L1 .tall (deg 7) > defaultCfg.L1 .tall (deg 3) := by
  rsa_predict

/-! ### Hearing "short" shifts height posterior downward

Mirror image: "short" shifts probability toward lower heights
(Section 4.3, Figure 6). -/

theorem short_shifts_downward :
    defaultCfg.L1 .short (deg 2) > defaultCfg.L1 .short (deg 8) := by
  rsa_predict

theorem short_shifts_downward' :
    defaultCfg.L1 .short (deg 3) > defaultCfg.L1 .short (deg 7) := by
  rsa_predict

-- ============================================================================
-- L1 Threshold Inference (Section 4.3, Figure 5)
-- ============================================================================

/-! ### Pragmatic sweet spot for thresholds

Given "tall," the listener infers a threshold that balances informativity and
plausibility (Figure 5, right panel). Very low thresholds (θ ≈ 0) make "tall"
uninformative (everything is tall), so the cost of speaking outweighs the
information gain. Very high thresholds (θ ≈ 9) make "tall" implausible
(almost nothing is tall). The posterior peaks at an intermediate θ.

This sweet spot requires utterance costs (Section 4.4: α=4, C(tall)=2);
without costs, L1_latent monotonically prefers lower thresholds. -/

theorem tall_threshold_peak_gt_low :
    defaultCfg.L1_latent .tall (thr 7) > defaultCfg.L1_latent .tall (thr 4) := by
  rsa_predict

theorem tall_threshold_peak_gt_high :
    defaultCfg.L1_latent .tall (thr 7) > defaultCfg.L1_latent .tall (thr 9) := by
  rsa_predict

-- ============================================================================
-- Context Sensitivity (§4.4, Figure 7)
-- ============================================================================

/-! ### Basketball context shifts height inference

When the reference class prior shifts right (basketball players: peak at h7
vs general population: peak at h5), L1 hearing "tall" assigns more probability
to taller heights (Figure 7). At h10, the basketball prior is 5× the general
prior (5 vs 1), which dominates the normalization penalty. -/

theorem basketball_tall_favors_taller :
    basketballCfg.L1 .tall (deg 10) > defaultCfg.L1 .tall (deg 10) := by
  rsa_predict

-- ============================================================================
-- Short Threshold Inference (§4.4, Figure 6)
-- ============================================================================

/-! ### Threshold posterior for "short"

Mirror of the "tall" threshold peak: given "short," the threshold posterior
peaks at an intermediate value too. Very high thresholds (θ ≈ 9) make "short"
nearly always true (uninformative, penalized by cost), very low thresholds
(θ ≈ 0) make "short" nearly always false (implausible). -/

theorem short_threshold_peak_gt_low :
    defaultCfg.L1_latent .short (thr 3) > defaultCfg.L1_latent .short (thr 7) := by
  rsa_predict

theorem short_threshold_peak_gt_high :
    defaultCfg.L1_latent .short (thr 3) > defaultCfg.L1_latent .short (thr 0) := by
  rsa_predict

-- ============================================================================
-- Prior Symmetry (§4.4, p. 3821)
-- ============================================================================

/-! ### Symmetry of "tall" and "short" posteriors

The paper predicts (p. 3821): "since the lexical entries of tall and short
in (22) and (23) differ only in the direction of the comparison with their
estimated threshold, and since the prior is symmetric, we should expect the
interpretation of Al is short to be symmetric along the prior mean."

We verify the precondition: the height prior is symmetric around h5. -/

/-- The height prior is symmetric around the mean h5:
    heightPrior(k) = heightPrior(10−k) for all k. -/
theorem heightPrior_symmetric :
    ∀ h : Height, heightPrior h = heightPrior (deg (10 - h.toNat)) := by
  native_decide

-- ============================================================================
-- Additional Context Sensitivity (§4.4, Figure 7)
-- ============================================================================

/-! ### Basketball context shifts short inference

The paper uses "two input priors with different means" for "tall." The same
mechanism should work for "short": when the reference class shifts rightward
(basketball players), hearing "short" should shift inference *less* toward
the low end (since basketball players are less likely to be short). -/

theorem basketball_short_less_extreme :
    defaultCfg.L1 .short (deg 0) > basketballCfg.L1 .short (deg 0) := by
  rsa_predict

end RSA.LassiterGoodman2017

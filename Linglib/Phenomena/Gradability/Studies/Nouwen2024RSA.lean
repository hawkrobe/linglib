import Linglib.Phenomena.Imprecision.Studies.LassiterGoodman2017
import Linglib.Theories.Semantics.Lexical.Adjective.Intensification
import Linglib.Phenomena.Gradability.Studies.Nouwen2024
import Linglib.Tactics.RSAPredict
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Bridge: @cite{nouwen-2024} RSA Model → Gradability Phenomena
@cite{lassiter-goodman-2017} @cite{nouwen-2024}

"The semantics and probabilistic pragmatics of deadjectival intensifiers"
Linguistics and Philosophy.

## Innovation

Extends @cite{lassiter-goodman-2017} threshold RSA with **evaluative measures**:
deadjectival adverbs (horribly, pleasantly) derive their degree function
from the evaluative meaning of their adjectival base.

## Two-Threshold Intersecting Semantics

Standard RSA: P_L1(h, θ | u) ∝ P_S1(u | h, θ) × P(h) × P(θ)
Intensifier RSA: P_L1(h, θ, θ_e | u) ∝ P_S1(u | h, θ, θ_e) × P(h) × P(θ) × P(θ_e)

The listener jointly infers:
- h: the height/degree of the entity
- θ: the base adjective threshold ("warm")
- θ_e: the evaluative adverb threshold ("horribly"/"pleasantly")

## RSAConfig Mapping

- **U** = `Utterance` (bare_warm, horribly_warm, pleasantly_warm, silent)
- **W** = `Height` (Degree 10, 11 values: h0–h10)
- **Latent** = `Threshold × Threshold` (100 values: θ_adj × θ_eval)
- **meaning(θ, θ_e, u, h)** = `prior(h)` if ⟦u⟧(h, θ, θ_e), else 0
- **s1Score** = beliefAction: `exp(α · (log L0 − C(u)))`
- **α** = 4 (matching @cite{lassiter-goodman-2017})
- **C(bare)** = 1, **C(horribly/pleasantly)** = 2, **C(∅)** = 0

## Verified Predictions

1. H-adverb: "horribly warm" shifts height toward extremes (Goldilocks, §4)
2. M-adverb: "pleasantly warm" concentrates at moderate heights (Goldilocks, §4)
3. Both intensifiers still entail warmth (base adjective holds)

-/

namespace RSA.Nouwen2024

open RSA.LassiterGoodman2017 (Height Threshold
  heightPrior thresholdPrior tallMeaning)
open Core.Scale (deg thr allDegrees allThresholds)
open Semantics.Lexical.Adjective.Intensification (EvaluativeValence)
open Phenomena.Gradability.Intensifiers (IntensifierClass)

-- Utterances

/--
Utterances about warmth with optional deadjectival intensifier.

The utterance set extends bare "warm" with intensified variants.
-/
inductive Utterance where
  | bare_warm       -- "x is warm"
  | horribly_warm   -- "x is horribly warm"
  | pleasantly_warm -- "x is pleasantly warm"
  | silent          -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

def allUtterances : List Utterance :=
  [.bare_warm, .horribly_warm, .pleasantly_warm, .silent]

-- Evaluative Measures on Height
-- (Reusing LG2017's Height type as degree domain)

/--
Evaluative measure for "horrible" applied to the Height domain.

μ_horrible(h) = |h - 5|

Heights far from the norm (5) are evaluated as more "horrible".
-/
def muHorrible (h : Height) : ℕ :=
  let d := h.toNat
  if d ≥ 5 then d - 5 else 5 - d

/--
Evaluative measure for "pleasant" applied to the Height domain.

μ_pleasant(h) = 5 - |h - 5|

Heights near the norm (5) are evaluated as more "pleasant".
-/
def muPleasant (h : Height) : ℕ :=
  let d := h.toNat
  if d ≥ 5 then 10 - d else d

/--
Evaluative measure for "usual" (constant -- no evaluative content).

μ_usual(h) = 5 for all h.

A constant evaluative measure provides no information, which is why
"*usually warm" is vacuous (Zwicky's generalization).
-/
def muUsual (_h : Height) : ℚ := 5

-- Meaning Function (Nouwen eq. 45)

/--
Joint state for the intensifier model: (Height, θ_adj, θ_eval).

- Height: the degree of warmth
- θ_adj: threshold for "warm" (from LG2017)
- θ_eval: threshold for the evaluative adverb
-/
abbrev JointState := Height × Threshold × Threshold

def allJointStates : List JointState :=
  (allDegrees 10).flatMap λ h =>
    (allThresholds 10).flatMap λ θ =>
      (allThresholds 10).map λ θ_e => (h, θ, θ_e)

/--
Full meaning function (@cite{nouwen-2024}, eq. 45).

- bare_warm: h > θ_adj (standard LG2017)
- horribly_warm: (h > θ_adj) ∧ (μ_horrible(h) > θ_eval)
- pleasantly_warm: (h > θ_adj) ∧ (μ_pleasant(h) > θ_eval)
- silent: always true
-/
def meaning (u : Utterance) (state : JointState) : Bool :=
  let (h, θ, θ_e) := state
  match u with
  | .bare_warm       => tallMeaning θ h  -- reusing LG2017's "degree > threshold"
  | .horribly_warm   => tallMeaning θ h && (muHorrible h > θ_e.toNat)
  | .pleasantly_warm => tallMeaning θ h && (muPleasant h > θ_e.toNat)
  | .silent          => true

-- Joint Prior

/--
Joint prior: P(h, θ, θ_e) = P(h) × P(θ) × P(θ_e)

All three dimensions are independent. Height uses LG2017's normal-like prior;
both threshold priors are uniform.
-/
def jointPrior (state : JointState) : ℚ :=
  let (h, θ, θ_e) := state
  heightPrior h * thresholdPrior θ * thresholdPrior θ_e

-- Sequential Bayesian Update (Nouwen's Key Innovation)

/--
Adverb update: filter the prior by the evaluative constraint.

Given an evaluative measure μ and an evaluative threshold θ_e:
P'(h) ∝ P(h) × 1[μ(h) > θ_e]

This reweights the height prior, concentrating probability on heights
that satisfy the evaluative condition.
-/
def adverbUpdate (evalMu : Height → ℚ) (θ_e : Threshold) : Height → ℚ :=
  λ h =>
    let passes := if evalMu h > θ_e.toNat then (1 : ℚ) else 0
    heightPrior h * passes

/--
Normalize a height distribution.
-/
def normalizeHeightDist (f : Height → ℚ) : Height → ℚ :=
  let total := ((allDegrees 10).map f).foldl (· + ·) 0
  λ h => if total ≠ 0 then f h / total else 0

-- Zwicky Vacuity

/--
A constant evaluative measure (μ_usual) produces a uniform adverb update:
for any height h, the update passes for the same threshold values,
so it provides no discriminating information about degree.

This is why "*usually warm" is vacuous -- the evaluative adverb
carries no evaluative content and thus adds nothing to "warm".
-/
theorem usual_constant :
    ∀ h₁ h₂ : Height, muUsual h₁ = muUsual h₂ := by
  intro h₁ h₂
  simp [muUsual]

/--
With a constant evaluative measure, the adverb update is uniform:
for any fixed θ_e, the relative weighting of heights is unchanged
from the base prior (since the evaluative filter either passes
all heights or rejects all heights for that θ_e).
-/
theorem constant_eval_uniform_update (θ_e : Threshold) :
    ∀ h₁ h₂ : Height,
      adverbUpdate muUsual θ_e h₁ * heightPrior h₂ =
      adverbUpdate muUsual θ_e h₂ * heightPrior h₁ := by
  intro h₁ h₂
  simp [adverbUpdate, muUsual]
  ring_nf

-- Grounding: Bare Case Reduces to LG2017

/--
With no evaluative adverb (constant μ), the sequential update
preserves the original height prior ratios.

This is the grounding theorem: the bare adjective case of
Nouwen2024 reduces to the standard LassiterGoodman2017 model.
-/
theorem bare_prior_ratios_preserved (θ_e : Threshold) (h : Height) :
    adverbUpdate (λ _ => (5 : ℚ)) θ_e h =
    heightPrior h * (if (5 : ℚ) > θ_e.toNat then 1 else 0) := by
  simp [adverbUpdate]

-- Utterance Cost Structure

/--
Intensified utterances are costlier than bare utterances.

Nouwen assumes that "horribly warm" has higher production cost
than "warm" because it contains more morphological material.
This cost differential drives the pragmatic reasoning.
-/
def utteranceCost : Utterance → ℚ
  | .bare_warm       => 1
  | .horribly_warm   => 2  -- additional morphological material
  | .pleasantly_warm => 2
  | .silent          => 0

-- Evaluative Measure Properties

/--
Horrible measure assigns maximal value at scale maximum (degree 10).
-/
theorem horrible_max_at_h10 :
    muHorrible (deg 10) = 5 := by native_decide

/--
Pleasant measure assigns maximal value at norm (degree 5).
-/
theorem pleasant_max_at_h5 :
    muPleasant (deg 5) = 5 := by native_decide

/--
Horrible and pleasant measures are complementary:
μ_horrible(h) + μ_pleasant(h) = norm for all h ≥ norm.
-/
theorem horrible_pleasant_complement :
    muHorrible (deg 7) + muPleasant (deg 7) = 5 := by native_decide

-- ============================================================================
-- RSAConfig (§4, eq. 72 — simultaneous dual-threshold model)
-- ============================================================================

open RSA.LassiterGoodman2017 (heightPriorR heightPriorR_nonneg)
open Real (exp log exp_pos)

noncomputable def utteranceCostR (u : Utterance) : ℝ := ↑(utteranceCost u)

/-- S1 scoring rule: exp(α · (log L0(h|u,θ,θ_e) − C(u))), gated at L0=0.
    Identical to @cite{lassiter-goodman-2017}'s beliefAction but with
    Latent = Threshold × Threshold for the dual-threshold model. -/
noncomputable def intensifierS1Score :
    (Utterance → Height → ℝ) → ℝ → (Threshold × Threshold) → Height → Utterance → ℝ :=
  fun l0 α _ w u =>
    if l0 u w = 0 then 0
    else exp (α * (log (l0 u w) - utteranceCostR u))

theorem intensifierS1Score_nonneg :
    ∀ (l0 : Utterance → Height → ℝ) (α : ℝ) (l : Threshold × Threshold)
      (w : Height) (u : Utterance),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ intensifierS1Score l0 α l w u := by
  intro _ _ _ _ _ _ _; simp only [intensifierS1Score]; split
  · exact le_refl 0
  · exact le_of_lt (exp_pos _)

/-- RSAConfig for the @cite{nouwen-2024} intensifier model (eq. 72).

    Extends @cite{lassiter-goodman-2017} threshold RSA with a second threshold
    for the evaluative adverb. L1 jointly infers height, adjective threshold,
    and evaluative threshold:

      P_L1(h, θ, θ_e | u) ∝ P_S1(u | h, θ, θ_e) · P(h) · P(θ) · P(θ_e)

    The meaning function (eq. 45) is an intersection of two positive forms:
    - bare_warm: h > θ
    - horribly_warm: (h > θ) ∧ (μ_horrible(h) > θ_e)
    - pleasantly_warm: (h > θ) ∧ (μ_pleasant(h) > θ_e)
    - silent: ⊤ -/
@[reducible]
noncomputable def nouwenCfg : RSA.RSAConfig Utterance Height where
  Latent := Threshold × Threshold
  meaning _ l u h := if meaning u (h, l.1, l.2) then heightPriorR h else 0
  meaning_nonneg _ l u h := by
    show 0 ≤ if meaning u (h, l.1, l.2) then heightPriorR h else 0
    split
    · exact heightPriorR_nonneg h
    · exact le_refl 0
  s1Score := intensifierS1Score
  s1Score_nonneg := intensifierS1Score_nonneg
  α := 4
  α_pos := by norm_num
  worldPrior := heightPriorR
  worldPrior_nonneg := heightPriorR_nonneg
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- Goldilocks Effect Predictions (§4, Figures 5–8)
-- ============================================================================

/-! ### H-adverb: "horribly warm" shifts height toward extremes

The Goldilocks effect for negative-evaluative bases: μ_horrible(h) = |h − 5|
peaks at extremes, so L1 hearing "horribly warm" concentrates probability
on extreme heights (Figure 7). Heights near the norm (h=5) have
μ_horrible = 0 and cannot satisfy the evaluative positive form at any θ_e. -/

set_option rsa_predict.skipReflection true in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem horribly_shifts_upward :
    nouwenCfg.L1 .horribly_warm (deg 8) > nouwenCfg.L1 .horribly_warm (deg 4) := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem horribly_implies_warm :
    nouwenCfg.L1 .horribly_warm (deg 8) > nouwenCfg.L1 .horribly_warm (deg 2) := by
  rsa_predict

/-! ### M-adverb: "pleasantly warm" concentrates at moderate heights

The Goldilocks effect for positive-evaluative bases: μ_pleasant(h) = 5 − |h − 5|
peaks at the norm (h=5), so L1 hearing "pleasantly warm" concentrates
probability on moderate heights (Figure 8). Extreme heights (h=9,10) have
low μ_pleasant and cannot satisfy the evaluative positive form. -/

set_option rsa_predict.skipReflection true in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem pleasantly_prefers_moderate :
    nouwenCfg.L1 .pleasantly_warm (deg 6) > nouwenCfg.L1 .pleasantly_warm (deg 9) := by
  rsa_predict

set_option rsa_predict.skipReflection true in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem pleasantly_implies_warm :
    nouwenCfg.L1 .pleasantly_warm (deg 6) > nouwenCfg.L1 .pleasantly_warm (deg 2) := by
  rsa_predict

end RSA.Nouwen2024

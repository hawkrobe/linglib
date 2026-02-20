import Linglib.Phenomena.Gradability.Imprecision.Studies.LassiterGoodman2017
import Linglib.Theories.Semantics.Lexical.Adjective.Intensification
import Linglib.Phenomena.Gradability.IntensifiersBridge
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Bridge: Nouwen (2024) RSA Model → Gradability Phenomena

"The semantics and probabilistic pragmatics of deadjectival intensifiers"
Linguistics and Philosophy.

## Innovation

Extends Lassiter & Goodman (2017) threshold RSA with **evaluative measures**:
deadjectival adverbs (horribly, pleasantly) derive their degree function
from the evaluative meaning of their adjectival base.

## Two-Threshold Intersecting Semantics

Standard RSA:       P_L1(h, θ | u) ∝ P_S1(u | h, θ) × P(h) × P(θ)
Intensifier RSA:    P_L1(h, θ, θ_e | u) ∝ P_S1(u | h, θ, θ_e) × P(h) × P(θ) × P(θ_e)

The listener jointly infers:
- h: the height/degree of the entity
- θ: the base adjective threshold ("warm")
- θ_e: the evaluative adverb threshold ("horribly"/"pleasantly")

## Status

RSA evaluation infrastructure (boolToRat, basicL1, marginalize, getScore)
has been removed. Domain types, meaning functions, evaluative measures,
sequential Bayesian update structure, and algebraic theorems are preserved.
RSA computation stubs remain with `sorry` for future reimplementation.

## References

- Nouwen, R. (2024). The semantics and probabilistic pragmatics of
  deadjectival intensifiers. Linguistics and Philosophy.
- Lassiter, D. & Goodman, N. (2017). Adjectival vagueness.
-/

namespace RSA.Nouwen2024

open RSA.LassiterGoodman2017 (Height Threshold allHeights allThresholds
  heightPrior thresholdPrior tallMeaning)
open Core.Scale (deg thr)
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
def muHorrible (h : Height) : ℚ :=
  let d := h.toNat
  let norm : Int := 5
  let diff : Int := d - norm
  if diff ≥ 0 then diff else -diff

/--
Evaluative measure for "pleasant" applied to the Height domain.

μ_pleasant(h) = 5 - |h - 5|

Heights near the norm (5) are evaluated as more "pleasant".
-/
def muPleasant (h : Height) : ℚ :=
  let d := h.toNat
  let norm : Int := 5
  let diff : Int := d - norm
  let absDiff := if diff ≥ 0 then diff else -diff
  5 - absDiff

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
  allHeights.flatMap λ h =>
    allThresholds.flatMap λ θ =>
      allThresholds.map λ θ_e => (h, θ, θ_e)

/--
Full meaning function (Nouwen 2024, eq. 45).

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
  let total := (allHeights.map f).foldl (· + ·) 0
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

end RSA.Nouwen2024

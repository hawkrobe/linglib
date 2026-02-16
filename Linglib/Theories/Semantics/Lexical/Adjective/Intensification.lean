/-
# Evaluative Measure Semantics for Deadjectival Intensifiers

Nouwen (2024) proposes that deadjectival intensifiers derive their degree
function from the evaluative meaning of their adjectival base.

## Core Idea

An evaluative adjective (e.g., "horrible") has a measure function μ that
assigns high values to degrees that are evaluated negatively.

For "horrible": μ_horrible(d) peaks at extreme degrees (far from the norm).
For "pleasant": μ_pleasant(d) peaks at moderate degrees (near the norm).

## Intensified Meaning (Nouwen eq. 45)

⟦horribly warm⟧ = λd. warm(d) ∧ horrible(d)

The intensified positive form is the conjunction (intersection) of:
1. The base adjective's positive meaning: d > θ_adj
2. The evaluative measure exceeding its own threshold: μ_eval(d) > θ_eval

## References

- Nouwen, R. (2024). The semantics and probabilistic pragmatics of
  deadjectival intensifiers. Linguistics and Philosophy.
- Kennedy, C. (2007). Vagueness and grammar.
- Lassiter, D. & Goodman, N. (2017). Adjectival vagueness.
-/

import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Mathlib.Data.Rat.Defs

namespace Semantics.Lexical.Adjective.Intensification

open Core.Scale (Degree Threshold Degree.toNat Threshold.toNat deg thr)
open Semantics.Lexical.Adjective (positiveMeaning)

-- Evaluative Valence (shared with Phenomena.Gradability.Intensifiers)

/--
Evaluative valence of an adjectival base.

This is distinct from scalar polarity (positive/negative scale direction):
- **positive**: the adjective denotes a good/desirable property (pleasant, nice)
- **negative**: the adjective denotes a bad/undesirable property (horrible, terrible)
- **neutral**: no inherent evaluative content (usual, possible)

Nouwen (2024) argues that evaluative valence, not scalar polarity,
determines the intensifier's degree class.
-/
inductive EvaluativeValence where
  | positive   -- pleasant, nice, decent
  | negative   -- horrible, terrible, awful
  | neutral    -- usual, possible (non-evaluative)
  deriving Repr, DecidableEq, BEq

-- Evaluative Measure Functions

/--
An evaluative measure function assigns a rational-valued "goodness of fit"
score to each degree on a scale.

- `form`: the adjectival base (e.g., "horrible")
- `valence`: evaluative valence from the Phenomena layer
- `mu`: the measure function μ : Nat → ℚ (takes degree's Nat value)

The measure function captures how well a degree matches the evaluative
meaning of the base adjective.
-/
structure EvaluativeMeasure (max : Nat) where
  form : String
  valence : EvaluativeValence
  mu : Nat → ℚ

/--
Evaluative measure for negative-evaluative bases (horrible, terrible, etc.).

μ_horrible(d) = |d - norm|

Peaks at extremes (d = 0 and d = max), lowest at the norm.
Negative-evaluative adjectives evaluate extreme degrees as more salient,
which is why "horribly warm" targets high degrees.
-/
def muHorrible (max : Nat) : EvaluativeMeasure max where
  form := "horrible"
  valence := .negative
  mu := λ d =>
    let norm : ℚ := max / 2
    let diff : ℚ := d - norm
    if diff ≥ 0 then diff else -diff

/--
Evaluative measure for positive-evaluative bases (pleasant, nice, etc.).

μ_pleasant(d) = norm - |d - norm|

Peaks at the norm (middle degrees), lowest at extremes.
Positive-evaluative adjectives evaluate moderate degrees as best,
which is why "pleasantly warm" targets moderate degrees.
-/
def muPleasant (max : Nat) : EvaluativeMeasure max where
  form := "pleasant"
  valence := .positive
  mu := λ d =>
    let norm : ℚ := max / 2
    let diff : ℚ := d - norm
    let absDiff := if diff ≥ 0 then diff else -diff
    norm - absDiff

-- Intensified Meaning (Nouwen eq. 45)

/--
Intensified positive meaning (Nouwen 2024, eq. 45).

⟦ADV-ly ADJ⟧(d, θ_adj, θ_eval) = (d > θ_adj) ∧ (μ_eval(d) > θ_eval)

The intensified form is the conjunction (intersection) of:
1. The base adjective's positive form: d > θ_adj
2. The evaluative threshold: μ_eval(d) > θ_eval
-/
def intensifiedMeaning {max : Nat}
    (eval : EvaluativeMeasure max) (d : Degree max) (θ_adj θ_eval : Threshold max) : Bool :=
  positiveMeaning d θ_adj && (eval.mu d.toNat > θ_eval.toNat)

-- Bridge Theorem: Intensified → Positive

/--
Intensified meaning entails the positive form.

If "horribly warm" is true, then "warm" is true.
This is because the intensified meaning is a conjunction that includes
the positive meaning as one conjunct.
-/
theorem intensified_implies_positive {max : Nat}
    (eval : EvaluativeMeasure max) (d : Degree max) (θ_adj θ_eval : Threshold max)
    (h : intensifiedMeaning eval d θ_adj θ_eval = true) :
    positiveMeaning d θ_adj = true := by
  simp [intensifiedMeaning] at h
  exact h.1

-- Structural Properties of Evaluative Measures

/--
The horrible measure peaks at extremes: μ(max) ≥ μ(norm).

Negative-evaluative adjectives assign highest values to extreme degrees.
-/
theorem muHorrible_peaks_at_extreme_10 :
    (muHorrible 10).mu 10 ≥ (muHorrible 10).mu 5 := by native_decide

/--
The pleasant measure peaks at norm: μ(norm) ≥ μ(max).

Positive-evaluative adjectives assign highest values to moderate degrees.
-/
theorem muPleasant_peaks_at_norm_10 :
    (muPleasant 10).mu 5 ≥ (muPleasant 10).mu 10 := by native_decide

/--
Goldilocks structural theorem: at extreme degrees (d = max),
the horrible measure exceeds the pleasant measure.

This is the semantic foundation of the Goldilocks effect:
extreme degrees are more "horrible" than "pleasant".
-/
theorem goldilocks_at_extreme_10 :
    (muHorrible 10).mu 10 ≥ (muPleasant 10).mu 10 := by native_decide

/--
Goldilocks structural theorem (converse): at moderate degrees (d = norm),
the pleasant measure exceeds the horrible measure.

Moderate degrees are more "pleasant" than "horrible".
-/
theorem goldilocks_at_norm_10 :
    (muPleasant 10).mu 5 ≥ (muHorrible 10).mu 5 := by native_decide

-- Valence–Class Bridge

/--
Bridge between evaluative valence and evaluative measure behavior:
negative-evaluative measures peak at extremes, positive at the norm.

This connects the Phenomena-layer `EvaluativeValence` to the
Theory-layer `EvaluativeMeasure` structural properties.
-/
theorem negative_valence_extreme_peak :
    (muHorrible 10).valence = .negative ∧
    (muHorrible 10).mu 10 ≥ (muHorrible 10).mu 5 :=
  ⟨rfl, muHorrible_peaks_at_extreme_10⟩

theorem positive_valence_norm_peak :
    (muPleasant 10).valence = .positive ∧
    (muPleasant 10).mu 5 ≥ (muPleasant 10).mu 10 :=
  ⟨rfl, muPleasant_peaks_at_norm_10⟩

end Semantics.Lexical.Adjective.Intensification

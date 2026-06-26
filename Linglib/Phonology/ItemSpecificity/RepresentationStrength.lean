import Linglib.Phonology.ItemSpecificity.Defs
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Representation Strength (Gradient Symbolic Representations)
[smolensky-goldrick-2016] [pierrehumbert-2001] [todd-pierrehumbert-hay-2019]

The "frequency lives in the lexicon, not the grammar" theory: the
grammar's weights are fixed; what varies with frequency is the
**activation strength** of the underlying representation. A
high-frequency item has a more robust UR; a low-frequency item has a
weakened UR more susceptible to deletion / repair / coalescence.

## Architectural backbone: S-G 2016 GSR

The gradient-activity machinery follows [smolensky-goldrick-2016].
A symbol's *activity* is a real-valued degree of presence — the /t/ at
the end of *petit* in their analysis is `0.5·t`, half-active. Surface
realization is decided by a Harmonic Grammar in which faithfulness
constraints (DEP, MAX) are scaled by activity, with the surfacing
condition for an intervocalic consonant being `χ > θ ≈ 0.73` where `χ`
is the total activity at that position (p. 20). Compounds combine
constituent activities **additively** via coalescence under MAX as a
positive constraint (their `χ = λ + τ` for the W₁-final + W₂-initial
blend in *petit ami*; p. 17 tableau, p. 20).

## Frequency channel: Pierrehumbert / TPH

S-G treat activity values as lexical constants ((λ, τ, ζ, ν) ≈
(0.5, 0.3, 0.3, 0.3) at p. 15) but invite a usage-based hybrid in
their §3.6: "Such frequency dependence motivates certain 'usage-' or
'construction-'based accounts of liaison; a formalization of a kind
of usage-based account will in fact be blended into the proposed
account." This file formalizes that hybrid: activity is a function of
token log-frequency, following [pierrehumbert-2001]'s
"resting activation level" primitive (TSL 45 p. 141: *"each exemplar
has an associated strength — which may be viewed as a resting
activation level"*). Direction-of-effect predictions follow
[todd-pierrehumbert-hay-2019]: high-frequency items are more
robustly recognized under acoustic ambiguity, with consequences that
depend on whether the category moves toward or away from a competitor.

## The schema, contrasted with `ScaledWeights`

| Theory             | What scales with log-frequency  | Where scaling lives |
|--------------------|---------------------------------|---------------------|
| ScaledWeights      | Constraint weight               | Grammar             |
| RepresentationStrength | Underlying-form activation  | Lexicon             |

Both can produce the same surface gradient on simplex datasets, but
they diverge on:

- **Cross-constraint coherence**: in ScaledWeights, each constraint
  has its own slope; in RepresentationStrength, all constraints
  inherit the same per-item activation, so frequency effects across
  constraints are coupled.
- **Compositional items**: in ScaledWeights, a compound's weight
  depends only on the compound's own frequency; in RepStrength under
  `addCombine`, a compound's surface activity is the *sum* of
  constituent activities (S-G coalescence), so a high-activity
  constituent can rescue a low-activity one.

## The Breiss-Katsuda-Kawahara N2-frequency effect

[breiss-katsuda-kawahara-2026] report that high N2 token
frequency in Japanese compounds *blocks* nasalisation (preserves the
boundary). They themselves analyze this with MaxEnt + Lexical
Conservatism ([steriade-2000]); the GSR + frequency-derived
activity hybrid here is one of several siblings consistent with the
pattern. Under this hybrid: high N2 frequency → high N2-initial
activity → activity threshold for faithful boundary preservation
(`χ > θ`) more easily met → less nasalisation. The prediction follows
from S-G's optimality condition without further machinery; cf.
`Studies/BreissKatsudaKawahara2026.lean` for the
discrimination across siblings.
-/

namespace Constraints.ItemSpecificity.RepStrength

open Constraints.ItemSpecificity

-- ============================================================================
-- § 1: Activation
-- ============================================================================

/-- The activation strength of an item: a sigmoid-like function of its
    log-frequency, bounded in [0, 1]. We model it abstractly here as a
    parameter; concrete instances pick a specific shape (logistic,
    cumulative, etc.). -/
def activation {α : Type} [HasTokenFreq α]
    (sigmoid : ℝ → ℝ) (a : α) : ℝ :=
  sigmoid (tokenLogFreq a)

/-- The standard logistic sigmoid `1 / (1 + exp (-(x - μ)))`. -/
noncomputable def logistic (μ : ℝ) (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-(x - μ)))

-- ============================================================================
-- § 2: Compositional activation (what distinguishes RepStrength from ScaledWeights)
-- ============================================================================

/-- The activation of a compound *inherits* from its constituents,
    rather than being looked up from the compound's own frequency. The
    inherit function (typically `min` or product) determines how
    constituent activations combine.

    This is the key architectural commitment: in
    RepresentationStrength, a high-frequency constituent boosts the
    compound's activation regardless of the compound's own frequency.
    Contrast with ScaledWeights, where constraint weights see only the
    candidate's own log-frequency. -/
def compoundActivation {α : Type} [HasTokenFreq α]
    (sigmoid : ℝ → ℝ) (combine : ℝ → ℝ → ℝ)
    (n1 n2 : α) : ℝ :=
  combine (activation sigmoid n1) (activation sigmoid n2)

/-- The **additive combine rule** matching [smolensky-goldrick-2016]'s
    coalescence: surface activity at the W₁-W₂ boundary is the sum of
    the constituents' contributions (their `χ = λ + τ`, p. 17, p. 20),
    arising from MAX as a positive constraint that rewards faithfulness
    scaled by underlying activity.

    This is the canonical combine rule for a GSR-grounded compound
    architecture; new consumers should prefer it over `minCombine`. -/
def addCombine (a b : ℝ) : ℝ := a + b

/-- The **minimum** combine rule — a non-S-G alternative. Predicts that
    compound activity is bounded above by the weakest constituent;
    closer in spirit to a Bybee-style storage account where compound
    accessibility cannot exceed the rarer constituent's accessibility.
    Useful as a separation contrast against `addCombine`; not licensed
    by S-G's coalescence mechanism. -/
def minCombine (a b : ℝ) : ℝ := min a b

end Constraints.ItemSpecificity.RepStrength

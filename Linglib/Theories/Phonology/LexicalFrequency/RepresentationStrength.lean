import Linglib.Theories.Phonology.LexicalFrequency.Defs
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Representation Strength (Gradient Symbolic Representations)
@cite{moore-cantwell-2021} @cite{smolensky-goldrick-2016}

The "frequency lives in the lexicon, not the grammar" theory: the
grammar's weights are fixed; what varies with frequency is the
**activation strength** of the underlying representation. A
high-frequency item has a more robust UR; a low-frequency item has a
weakened UR more susceptible to deletion / repair / coalescence.

The schema is dual to `ScaledWeights`:

| Theory             | What scales with log-frequency  | Where scaling lives |
|--------------------|--------------------------------|---------------------|
| ScaledWeights      | Constraint weight              | Grammar             |
| RepresentationStrength | Underlying-form activation | Lexicon             |

Both can produce the same surface gradient on simplex datasets, but
they diverge on:

- **Cross-constraint coherence**: in ScaledWeights, each constraint has
  its own slope; in RepresentationStrength, all constraints inherit the
  same per-item activation, so frequency effects across constraints are
  coupled.
- **Compositional items**: in ScaledWeights, a compound's weight depends
  only on the compound's frequency; in RepresentationStrength, a
  compound's URs are inherited from its constituents, so the frequency
  channel is structural.

The Breiss-Katsuda-Kawahara N2-frequency effect (high N2 frequency
→ *less* nasalisation) is a clean RepresentationStrength prediction:
a high-activation N2 boundary is preserved, blocking the nasalisation
that would obliterate it.
-/

namespace Phonology.LexicalFrequency.RepStrength

open Phonology.LexicalFrequency

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

/-- The minimum-activation combine rule: a compound is only as
    represented-strongly as its weakest constituent. Predicts that a
    bound (low-activation) N2 cannot be propped up by its compound's
    high frequency — exactly the cross-cutting prediction the
    Breiss-Katsuda-Kawahara compounds exploit. -/
def minCombine (a b : ℝ) : ℝ := min a b

end Phonology.LexicalFrequency.RepStrength

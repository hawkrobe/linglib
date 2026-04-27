import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Theories.Pragmatics.RSA.LatentOperators
import Linglib.Phenomena.Negation.Studies.TesslerFranke2020
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{tessler-franke-2019} on mathlib `PMF` (Shape B + cost-factor migration)
@cite{tessler-franke-2019}

PMF-shaped re-formalisation of `TesslerFranke2020.lean`'s 6 findings. This is
the **first PMF migration with a cost factor in the S1 score**:
`S1(u | w) ∝ L0(w | u)^α · exp(−C(u))`. Validates that `RSA.S1Belief`'s
`costFactor : U → ℝ≥0∞` argument handles the canonical `exp(-cost)` shape.

## Friction surfaced (informs API direction)

- **Cost factor as ENNReal**: `exp (-utteranceCost u)` lives in `ℝ` — needs
  lift to `ℝ≥0∞` via `ENNReal.ofReal`. Pattern from `Nouwen2024PMF.lean`.
- **32-state latent**: `Latent := HThreshold × HThreshold × NegLexicon`
  (4×4×2). The per-latent leaves are 32-case case-bashes — well beyond
  hand-discharge. Validates the need for `pmf_score_compare` tactic.
- **Shape D mixture**: finding `not_unhappy_more_positive_than_not_happy`
  compares `L1 .notUnhappy (deg 3) > L1 .notHappy (deg 3)` — same world,
  DIFFERENT observation. Different from same-observation Shape B; needs
  cross-observation API analysis. (Not the same as cross-utterance tsum
  Shape D either.)

## Reused from `TesslerFranke2020.lean`

* `HappinessDeg`, `HThreshold`, `Utterance`, `NegLexicon`, `LatentState`
* `utteranceMeaning`, `utteranceCost`
-/

set_option autoImplicit false

namespace TesslerFranke2020.PMF

open scoped ENNReal
open Core.Scale (Degree Threshold deg thr)

instance : Nonempty HappinessDeg := ⟨deg 0⟩
instance : Nonempty Utterance := ⟨.happy⟩
instance : Nonempty LatentState := ⟨(thr 0, thr 0, .contrary)⟩

/-! ## §1. L0 — uniform on extension via `RSA.L0OfBoolMeaning` -/

/-- Lexicon as a function from latent state. -/
abbrev meaningAt (l : LatentState) : Utterance → HappinessDeg → Bool :=
  utteranceMeaning l.1 l.2.1 l.2.2

/-- Extension of `meaningAt l u`. -/
abbrev extension (l : LatentState) (u : Utterance) : Finset HappinessDeg :=
  RSA.extensionOf (meaningAt l) u

-- (Most utterances have a non-empty extension at typical latent states.
-- The exception is e.g. .happy with θ₁ = 4 — degenerate case. We won't
-- need extension_nonempty in full generality; consumer findings only invoke
-- specific (l, u) pairs that ARE non-empty.)

/-! ## §2. S1Belief — cost-bearing speaker via `RSA.S1Belief`

The cost factor: `exp (-utteranceCost u)`. Cast to `ℝ≥0∞`. -/

noncomputable def costFactor (u : Utterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(utteranceCost u : ℝ)))

theorem costFactor_pos (u : Utterance) : costFactor u ≠ 0 := by
  unfold costFactor
  exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)

theorem costFactor_finite (u : Utterance) : costFactor u ≠ ∞ := by
  unfold costFactor
  exact ENNReal.ofReal_ne_top

/-! ## §3. Per-latent L0 + S1g + marginalSpeaker — sketch only

The per-latent S1g would be `RSA.S1Belief (L0_at l) costFactor 1`, marginalized
over `LatentState` via `RSA.marginalizeKernel` against a uniform latent prior.
Then L1 = `PMF.posterior` against uniform world prior.

The structural shell follows the ScontrasPearl template exactly. The leaves
(per-latent comparisons across 32 states) are well beyond hand-discharge
without the `pmf_score_compare` tactic.

This file is a placeholder + friction documentation. Full migration deferred
pending tactic infrastructure. -/

/-- Stub: full PMF L1 construction would go here following ScontrasPearl
template. -/
example : True := trivial

end TesslerFranke2020.PMF

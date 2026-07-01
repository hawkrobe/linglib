import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Semantics.Degree.Basic
import Linglib.Features.Antonymy
import Mathlib.Probability.Distributions.Uniform

/-!
# [tessler-franke-2019] on mathlib `PMF` (Shape B + cost-factor migration)
[tessler-franke-2019]

PMF-shaped formalisation of the paper's 6 findings. The **first PMF
migration with a cost factor in the S1 score**:
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
  cross-observation API analysis.
-/

set_option autoImplicit false

namespace TesslerFranke2020.PMF

open scoped ENNReal
open Degree (Degree Threshold deg thr)
open Features (NegationType)
open Degree (positiveMeaning negativeMeaning)

/-! ## §0. Domain types -/

/-- Happiness degree: 0 (miserable) to 4 (ecstatic). -/
abbrev HappinessDeg := Degree 4

instance : NeZero (4 : Nat) := ⟨by omega⟩

/-- Threshold values 0–3, used for both θ₁ (positive) and θ₂ (contrary). -/
abbrev HThreshold := Threshold 4

inductive Utterance where
  | happy       -- "is happy"
  | notHappy    -- "is not happy"
  | unhappy     -- "is unhappy"
  | notUnhappy  -- "is not unhappy"
  deriving Repr, DecidableEq, Fintype

/-- Lexicon for morphological negation "un-": contrary (polar opposite with
gap) vs contradictory (complement). Aliased to `Features.NegationType`. -/
abbrev NegLexicon := NegationType

/-- Joint latent state: (θ₁, θ₂, L) — 4 × 4 × 2 = 32 latent states. -/
@[reducible] def LatentState := HThreshold × HThreshold × NegLexicon

/-- Utterance meaning parameterized by thresholds and lexicon, grounded in
shared `Degree` predicates. -/
def utteranceMeaning (θ₁ θ₂ : HThreshold) (L : NegLexicon)
    (u : Utterance) (d : HappinessDeg) : Bool :=
  match u with
  | .happy => positiveMeaning d θ₁
  | .notHappy => !positiveMeaning d θ₁
  | .unhappy => match L with
    | .contrary => negativeMeaning d θ₂
    | .contradictory => !positiveMeaning d θ₁
  | .notUnhappy => match L with
    | .contrary => !negativeMeaning d θ₂
    | .contradictory => positiveMeaning d θ₁

/-- Utterance cost (morphological complexity): `C(un-) = 2`, `C(not) = 3`,
combined additively. -/
def utteranceCost (u : Utterance) : ℚ :=
  match u with
  | .happy => 0
  | .unhappy => 2
  | .notHappy => 3
  | .notUnhappy => 5

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

import Linglib.Core.Optimization.System
import Linglib.Phonology.Constraints.Weighted
import Linglib.Core.Optimization.Profile
import Linglib.Phonology.Constraints.Defs

/-!
# Constraint Systems — HG/MaxEnt instantiations of `Core.Optimization.ConstraintSystem`

The framework-neutral `ConstraintSystem` record + `predict` machinery
lives in `Core/Optimization/System.lean`. This file packages the
framework-neutral constraint-based grammar instantiations as smart
constructors:

  - `otSystem`     — OT: `Score = LexProfile Nat n`, decoder = `argminDecoder`
  - `hgSystem`     — HG: `Score = ℝ`, decoder = `argmaxDecoder`
  - `maxEntSystem` — MaxEnt: `Score = ℝ`, decoder = `softmaxDecoder α`

Stochastic frameworks that put noise on weights or candidates (NHG,
Normal MaxEnt, Stochastic OT) are RUM specializations: the noise kernel
composes with the deterministic decoder. See `NoiseKernel.lean`.

The OT-specific view — that the established `Tableau` API is `argminDecoder`
over a `ViolationProfile` score in disguise — lives in
`OptimalityTheory.Predict` (`tableauSystem`), keeping this file independent of
the OT layer.
-/

namespace Constraints

open Core.Optimization

-- ============================================================================
-- § 1: Smart Constructors
-- ============================================================================

variable {Cand : Type*}

/-- Build an Optimality Theory system: lexicographic minimum on a violation
    profile. The candidate set must be finite; `profile c` gives the
    `n`-tuple of constraint violations for candidate `c` ranked in
    order of dominance.

    Equivalent to choosing the OT winner(s) by `argmin` on the lex order. -/
noncomputable def otSystem {n : Nat}
    (candidates : Finset Cand) (profile : Cand → LexProfile Nat n) :
    ConstraintSystem Cand (LexProfile Nat n) where
  candidates := candidates
  score := profile
  decoder := argminDecoder

/-- Build a (deterministic) Harmonic Grammar system: real-valued harmony
    score, choose the candidate(s) that maximise it.

    The harmony score is `harmonyScoreR constraints c = -Σⱼ wⱼ · Cⱼ(c)`.
    Higher harmony = lower (weighted) violation = more grammatical. -/
noncomputable def hgSystem
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand)) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := argmaxDecoder

/-- Build a MaxEnt Harmonic Grammar system: same harmony score as `hgSystem`,
    but soft-decode with temperature `α`. As `α → ∞`, this converges to
    `hgSystem` (see `softmax_argmax_limit` in `Core.Agent.RationalAction`).

    The default `α = 1` matches [goldwater-johnson-2003]'s
    standard MaxEnt formulation. -/
noncomputable def maxEntSystem
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand))
    (α : ℝ := 1) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := softmaxDecoder α

end Constraints

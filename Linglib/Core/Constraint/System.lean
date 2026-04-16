import Linglib.Core.Constraint.Decoder
import Linglib.Core.Constraint.Weighted
import Linglib.Core.Constraint.Profile

/-!
# Constraint Systems — The Unified Interface

A `ConstraintSystem` packages the three components of any
constraint-based grammar into a single record:

  1. a finite **candidate** set,
  2. a **score** function (whatever value type the framework needs), and
  3. a **decoder** that turns scored candidates into a probability
     distribution.

```
  Candidates  ──score──▶  Score   ──decoder──▶   P : Cand → ℝ
```

Different frameworks differ only in *what they pick for each component*.
Smart constructors below assemble the standard frameworks:

  - `otSystem`     — OT: `Score = LexProfile Nat n`, decoder = `argminDecoder`
  - `hgSystem`     — HG: `Score = ℝ`, decoder = `argmaxDecoder`
  - `maxEntSystem` — MaxEnt: `Score = ℝ`, decoder = `softmaxDecoder α`

Every system exposes a single `predict` operation, so downstream code
can compare frameworks (or replace one with another) without touching
the rest of the analysis.

Stochastic frameworks that put noise on weights or candidates
(NHG, Normal MaxEnt, Stochastic OT) are RUM specializations: the
noise kernel composes with the deterministic decoder. Those live in
`NoiseKernel.lean` (forthcoming).
-/

namespace Core.Constraint

-- ============================================================================
-- § 1: ConstraintSystem
-- ============================================================================

/-- A constraint-based grammar: candidate set + score function + decoder.

    `Cand` is the candidate type (often something like an output form,
    a syntactic structure, or an input/output pair). `Score` is whatever
    value the constraints aggregate to — `ℝ` for HG/MaxEnt, `LexProfile
    Nat n` for OT, etc. -/
structure ConstraintSystem (Cand : Type*) (Score : Type*) where
  /-- The finite set of candidates this system evaluates. -/
  candidates : Finset Cand
  /-- The aggregated score for each candidate. -/
  score : Cand → Score
  /-- The choice rule: scored candidates → probability distribution. -/
  decoder : Decoder Cand Score

namespace ConstraintSystem

variable {Cand : Type*} {Score : Type*}

/-- The predicted probability of each candidate. -/
def predict (s : ConstraintSystem Cand Score) : Cand → ℝ :=
  s.decoder.decode s.candidates s.score

/-- A system whose decoder is `IsProb` produces non-negative predictions. -/
theorem predict_nonneg (s : ConstraintSystem Cand Score)
    [Decoder.IsProb s.decoder] (c : Cand) :
    0 ≤ s.predict c :=
  Decoder.IsProb.nonneg s.candidates s.score c

/-- A system whose decoder is `IsProb` predicts a probability distribution
    over its candidate set. -/
theorem predict_sum_eq_one (s : ConstraintSystem Cand Score)
    [Decoder.IsProb s.decoder] (hne : s.candidates.Nonempty) :
    ∑ c ∈ s.candidates, s.predict c = 1 :=
  Decoder.IsProb.sum_eq_one hne s.score

end ConstraintSystem

-- ============================================================================
-- § 2: Smart Constructors
-- ============================================================================

/-- Build an Optimality Theory system: lexicographic minimum on a violation
    profile. The candidate set must be finite; `profile c` gives the
    `n`-tuple of constraint violations for candidate `c` ranked in
    order of dominance.

    Equivalent to choosing the OT winner(s) by `argmin` on the lex order. -/
noncomputable def otSystem {Cand : Type*} {n : Nat}
    (candidates : Finset Cand) (profile : Cand → LexProfile Nat n) :
    ConstraintSystem Cand (LexProfile Nat n) where
  candidates := candidates
  score := profile
  decoder := argminDecoder

/-- Build a (deterministic) Harmonic Grammar system: real-valued harmony
    score, choose the candidate(s) that maximise it.

    The harmony score is `harmonyScoreR constraints c = -Σⱼ wⱼ · Cⱼ(c)`.
    Higher harmony = lower (weighted) violation = more grammatical. -/
noncomputable def hgSystem {Cand : Type}
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand)) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := argmaxDecoder

/-- Build a MaxEnt Harmonic Grammar system: same harmony score as `hgSystem`,
    but soft-decode with temperature `α`. As `α → ∞`, this converges to
    `hgSystem` (see `softmax_argmax_limit` in `Core.Agent.RationalAction`).

    The default `α = 1` matches @cite{goldwater-johnson-2003}'s
    standard MaxEnt formulation. -/
noncomputable def maxEntSystem {Cand : Type}
    (candidates : Finset Cand) (constraints : List (WeightedConstraint Cand))
    (α : ℝ := 1) :
    ConstraintSystem Cand ℝ where
  candidates := candidates
  score := harmonyScoreR constraints
  decoder := softmaxDecoder α

end Core.Constraint

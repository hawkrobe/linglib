import Linglib.Core.Logic.OT
import Mathlib.Data.Real.Basic

/-!
# Weighted Constraints — Generic Foundation

The shared foundation for any constraint framework that assigns numerical
**weights** to constraints and aggregates them into a single scalar score:
- Harmonic Grammar @cite{smolensky-legendre-2006}
- MaxEnt @cite{goldwater-johnson-2003}
- Noisy HG @cite{boersma-pater-2016}
- Normal MaxEnt @cite{flemming-2021}

A `WeightedConstraint C` extends `NamedConstraint C` (from `Core.Logic.OT`)
with a rational `weight`. The `harmonyScore` of a candidate is the negated
weighted sum of its violations: `H(c) = -Σⱼ wⱼ · Cⱼ(c)`.

These definitions are framework-agnostic — they make no commitment to
phonology, syntax, or any specific candidate type. Aggregator/Chooser
modules in `Core.Constraint.*` consume them; framework-specific wrappers
(MaxEnt, NHG, ...) live in their respective theory directories.
-/

namespace Core.Constraint

open Core.OT

-- ============================================================================
-- § 1: Weighted Constraints
-- ============================================================================

/-- A weighted constraint over candidates of type `C`.
    Extends `NamedConstraint C` with a rational-valued weight. -/
structure WeightedConstraint (C : Type) extends NamedConstraint C where
  /-- Constraint weight (higher = more important). -/
  weight : ℚ

/-- Harmony score: `H(c) = -Σⱼ wⱼ · Cⱼ(c)` (rational, computable).

    Negative because violations are penalized. With `wⱼ ≥ 0`, harmony
    decreases monotonically as a candidate accumulates violations. -/
def harmonyScore {C : Type} (constraints : List (WeightedConstraint C)) (c : C) : ℚ :=
  constraints.foldl (λ acc con => acc - con.weight * (con.eval c : ℚ)) 0

/-- Harmony score as a real number, for interfacing with `softmax` and
    other ℝ-valued machinery (rate-distortion bounds, `Real.exp`, etc.). -/
noncomputable def harmonyScoreR {C : Type}
    (constraints : List (WeightedConstraint C)) (c : C) : ℝ :=
  (harmonyScore constraints c : ℝ)

end Core.Constraint

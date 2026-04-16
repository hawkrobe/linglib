import Linglib.Core.Logic.OT
import Mathlib.Data.Real.Basic

/-!
# Harmonic Grammar: Basic Definitions @cite{smolensky-legendre-2006}

The shared foundation for all stochastic Harmonic Grammar variants:
Maximum Entropy (MaxEnt), Noisy HG (NHG), and Normal MaxEnt.

A Harmonic Grammar assigns numerical **weights** to constraints. The
**harmony score** of a candidate is the negated weighted sum of its
constraint violations: `H(c) = -Σⱼ wⱼ · Cⱼ(c)`.

Different stochastic variants map harmony scores to probabilities via
different mechanisms:
- **MaxEnt** (@cite{goldwater-johnson-2003}): `P(c) ∝ exp(H(c))` (softmax)
- **NHG** (@cite{boersma-pater-2016}): add Gaussian noise to weights
- **Normal MaxEnt** (@cite{flemming-2021}): add i.i.d. Gaussian noise to candidates

All three share the `WeightedConstraint` and `harmonyScore` definitions.
-/

namespace Phonology.HarmonicGrammar

open Core.OT

-- ============================================================================
-- § 1: Weighted Constraints
-- ============================================================================

/-- A weighted constraint for Harmonic Grammar.
    Extends `NamedConstraint` with a rational-valued weight. -/
structure WeightedConstraint (C : Type) extends NamedConstraint C where
  /-- Constraint weight (higher = more important). -/
  weight : ℚ

/-- Harmony score: H(c) = -Σⱼ wⱼ · Cⱼ(c).
    Negative because violations are penalized. -/
def harmonyScore {C : Type} (constraints : List (WeightedConstraint C)) (c : C) : ℚ :=
  constraints.foldl (λ acc con => acc - con.weight * (con.eval c : ℚ)) 0

/-- Harmony score as a real number, for interfacing with `softmax`. -/
noncomputable def harmonyScoreR {C : Type}
    (constraints : List (WeightedConstraint C)) (c : C) : ℝ :=
  (harmonyScore constraints c : ℝ)

end Phonology.HarmonicGrammar

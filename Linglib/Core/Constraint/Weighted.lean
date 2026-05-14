import Linglib.Core.Constraint.OT.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Weighted Constraints — Generic Foundation

The shared foundation for any constraint framework that assigns numerical
**weights** to constraints and aggregates them into a single scalar score:
- Harmonic Grammar @cite{smolensky-legendre-2006}
- MaxEnt @cite{goldwater-johnson-2003}
- Noisy HG @cite{boersma-pater-2016}
- Normal MaxEnt @cite{flemming-2021}

A `WeightedConstraint C` extends `NamedConstraint C` (from `Core.Constraint.OT`)
with a rational `weight`. The `harmonyScore` of a candidate is the negated
weighted sum of its violations: `H(c) = -Σⱼ wⱼ · Cⱼ(c)`.

These definitions are framework-agnostic — they make no commitment to
phonology, syntax, or any specific candidate type. Aggregator/Chooser
modules in `Core.Constraint.*` consume them; framework-specific wrappers
(MaxEnt, NHG, ...) live in their respective theory directories.
-/

namespace Core.Constraint

open Core.Constraint.OT

-- ============================================================================
-- § 1: Weighted Constraints
-- ============================================================================

/-- A weighted constraint over candidates of type `C`.
    Extends `NamedConstraint C` with a rational-valued weight. -/
structure WeightedConstraint (C : Type*) extends NamedConstraint C where
  /-- Constraint weight (higher = more important). -/
  weight : ℚ

/-- Harmony score: `H(c) = -Σⱼ wⱼ · Cⱼ(c)` (rational, computable).

    Negative because violations are penalized. With `wⱼ ≥ 0`, harmony
    decreases monotonically as a candidate accumulates violations. -/
def harmonyScore {C : Type*} (constraints : List (WeightedConstraint C)) (c : C) : ℚ :=
  constraints.foldl (λ acc con => acc - con.weight * (con.eval c : ℚ)) 0

/-- Harmony score as a real number, for interfacing with `softmax` and
    other ℝ-valued machinery (rate-distortion bounds, `Real.exp`, etc.). -/
noncomputable def harmonyScoreR {C : Type*}
    (constraints : List (WeightedConstraint C)) (c : C) : ℝ :=
  (harmonyScore constraints c : ℝ)

-- ============================================================================
-- § 2: ℚ ↔ ℝ Cast Lemmas
-- ============================================================================

/-! `harmonyScoreR` is just `(harmonyScore : ℝ)`. The lemmas below let
study files state ranking facts in the computable ℚ world (where
`native_decide`/`decide` work) and lift them to the ℝ world where the
softmax / `predict` API lives, without writing the
`show (harmonyScore _ : ℝ) < … from by exact_mod_cast …` boilerplate. -/

/-- The defining cast equation for `harmonyScoreR`: it is just the
    real-valued cast of `harmonyScore`. -/
theorem harmonyScoreR_eq_cast {C : Type*}
    (constraints : List (WeightedConstraint C)) (c : C) :
    harmonyScoreR constraints c = (harmonyScore constraints c : ℝ) := rfl

/-- `<` lifts from ℚ-valued `harmonyScore` to ℝ-valued `harmonyScoreR`. -/
theorem harmonyScoreR_lt_iff_harmonyScore_lt {C : Type*}
    (constraints : List (WeightedConstraint C)) (a b : C) :
    harmonyScoreR constraints a < harmonyScoreR constraints b ↔
    harmonyScore constraints a < harmonyScore constraints b := by
  unfold harmonyScoreR; exact Rat.cast_lt (K := ℝ)

/-- `=` lifts from ℚ-valued `harmonyScore` to ℝ-valued `harmonyScoreR`. -/
theorem harmonyScoreR_eq_iff_harmonyScore_eq {C : Type*}
    (constraints : List (WeightedConstraint C)) (a b : C) :
    harmonyScoreR constraints a = harmonyScoreR constraints b ↔
    harmonyScore constraints a = harmonyScore constraints b := by
  unfold harmonyScoreR; exact (Rat.cast_injective (α := ℝ)).eq_iff

-- ============================================================================
-- § 3: Harmony Comparison Predicate
-- ============================================================================

/-- `a` strictly dominates `b` in harmony when `H(a) > H(b)`.

    A computable, decidable shorthand for the common pattern of
    discharging score-comparison facts by `decide` / `native_decide`
    before lifting to the ℝ-valued `harmonyScoreR` for use with `softmax`.

    Naming note: this is a strict harmony ordering, not a probability-mass
    claim. Higher harmony does imply higher MaxEnt probability *under a
    fixed partition function* (since `exp` is monotone), but mass-
    distribution content (ganging, free-variation rates) is not captured
    by a strict predicate. -/
def harmonyDominates {C : Type*}
    (constraints : List (WeightedConstraint C)) (a b : C) : Prop :=
  harmonyScore constraints a > harmonyScore constraints b

instance {C : Type*} (constraints : List (WeightedConstraint C)) (a b : C) :
    Decidable (harmonyDominates constraints a b) :=
  inferInstanceAs (Decidable (harmonyScore constraints a > harmonyScore constraints b))

/-- Lift a `harmonyDominates` ranking fact (a ℚ-level harmony comparison,
    typically discharged by `decide`) into the ℝ-level harmony comparison
    required by `predict_softmax_lt_of_score_lt`.

    Argument-order note: `harmonyDominates _ a b` says `H(a) > H(b)`, which
    in `<` form reads `H(b) < H(a)` — hence the conclusion places `b` on
    the left and `a` on the right. -/
theorem harmonyScoreR_lt_of_dominates {C : Type*}
    {constraints : List (WeightedConstraint C)} {a b : C}
    (h : harmonyDominates constraints a b) :
    harmonyScoreR constraints b < harmonyScoreR constraints a :=
  (harmonyScoreR_lt_iff_harmonyScore_lt _ _ _).mpr h

end Core.Constraint

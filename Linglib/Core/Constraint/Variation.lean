import Linglib.Core.Constraint.Weighted

/-!
# MaxEnt Gradient Variation
@cite{goldwater-johnson-2003}

Predicates for reasoning about gradient phonological variation in
Maximum Entropy Harmonic Grammar. Since exp is monotone, the harmony
ordering directly determines the probability ordering:

  `H(a) > H(b)  ⟺  P(a) > P(b)`

This makes `moreProbable` a computable, decidable proxy for
probability comparison without requiring real-number arithmetic.
-/

namespace Core.Constraint

-- ============================================================================
-- § 1: Probability Ordering
-- ============================================================================

/-- One candidate is more probable than another under a MaxEnt grammar
    when its harmony score is strictly higher.

    Justified by monotonicity of exp: `exp(H(a)) > exp(H(b)) ⟺ H(a) > H(b)`,
    so harmony ordering = probability ordering. The general softmax
    inequality lives in `System.lean` as `predict_softmax_lt_of_score_lt`;
    `moreProbable` is the computable ℚ-level statement that
    `harmonyScoreR_lt_of_moreProbable` lifts into ℝ for use with `predict`. -/
@[reducible]
def moreProbable {C : Type} (constraints : List (WeightedConstraint C))
    (a b : C) : Prop :=
  harmonyScore constraints a > harmonyScore constraints b

/-- Lift a `moreProbable` ranking fact (a ℚ-level harmony comparison,
    typically discharged by `native_decide`) into the ℝ-level harmony
    comparison required by `predict_softmax_lt_of_score_lt`. -/
theorem harmonyScoreR_lt_of_moreProbable {C : Type}
    {constraints : List (WeightedConstraint C)} {a b : C}
    (h : moreProbable constraints a b) :
    harmonyScoreR constraints b < harmonyScoreR constraints a := by
  unfold harmonyScoreR
  exact_mod_cast h

end Core.Constraint

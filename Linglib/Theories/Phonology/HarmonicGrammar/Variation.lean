import Linglib.Theories.Phonology.HarmonicGrammar.Basic

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

namespace Theories.Phonology.HarmonicGrammar

-- ============================================================================
-- § 1: Probability Ordering
-- ============================================================================

/-- One candidate is more probable than another under a MaxEnt grammar
    when its harmony score is strictly higher.

    Justified by monotonicity of exp: `exp(H(a)) > exp(H(b)) ⟺ H(a) > H(b)`,
    so harmony ordering = probability ordering. -/
@[reducible]
def moreProbable {C : Type} (constraints : List (WeightedConstraint C))
    (a b : C) : Prop :=
  harmonyScore constraints a > harmonyScore constraints b

end Theories.Phonology.HarmonicGrammar

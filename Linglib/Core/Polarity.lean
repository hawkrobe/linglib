/-!
# Sentence Polarity

Binary sentence polarity: positive (affirmative) vs negative.

Used across phenomena involving polarity-sensitive behavior:
multiplicity inferences, homogeneity gaps, scalar implicatures, etc.

Note: This is distinct from other polarity-like distinctions in the library:
- `Core.Lexical.UD.Polarity` — morphological feature (`.Pos`/`.Neg`)
- `Semantics.Focus.Particles.Polarity` — monotonicity direction (`.up`/`.down`)
- `Pragmatics.NeoGricean.Evaluativity.Polarity` — adjective markedness
- `Semantics.Presupposition.OntologicalPreconditions.Polarity` — event assertion (`.affirmed`/`.negated`)
-/

namespace Core

/--
Sentence polarity: whether a sentence is affirmative or negated.
-/
inductive Polarity where
  | positive
  | negative
  deriving Repr, DecidableEq, BEq, Inhabited

end Core

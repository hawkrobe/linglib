/-!
# Sentence Polarity

Binary sentence polarity: positive (affirmative) vs negative.

Used across phenomena involving polarity-sensitive behavior:
multiplicity inferences, homogeneity gaps, scalar implicatures, etc.

Note: This is distinct from other polarity-like distinctions in the library:
- `Core.Lexical.UD.Polarity` — morphological feature (`.Pos`/`.Neg`)
- `NaturalLogic.ContextPolarity` — monotonicity direction (`.upward`/`.downward`)
- `Rett2015Implicature.Polarity` — adjective markedness
- `Semantics.Presupposition.Preconditions.EventSentence.polarity` — polarity of the event claim
-/

namespace Features

/--
Sentence polarity: whether a sentence is affirmative or negated.
-/
inductive Polarity where
  | positive
  | negative
  deriving Repr, DecidableEq, Inhabited

end Features

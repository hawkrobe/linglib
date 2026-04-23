/-!
# EvaluativeValence — Good/Bad/Neutral Classification of Gradable Predicates

@cite{nouwen-2024}

Distinct from scalar polarity (positive/negative scale direction):

* **positive** — denotes a good/desirable property (*pleasant, nice, good*)
* **negative** — denotes a bad/undesirable property (*horrible, terrible, bad*)
* **neutral** — no inherent evaluative content (*usual, possible, tall*)

@cite{nouwen-2024} argues that evaluative valence, not scalar polarity,
determines the intensifier degree class (the *Goldilocks* effect):
negative-evaluative bases yield H-degree intensifiers, positive-
evaluative bases yield M-degree intensifiers.
-/

namespace Features

/-- Evaluative valence of a gradable predicate. -/
inductive EvaluativeValence where
  | positive
  | negative
  | neutral
  deriving Repr, DecidableEq

end Features

import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Quantifier typology — shared enums
[horn-1972] [barwise-cooper-1981]

Theory-level descriptive enums for the typological classification of
quantifiers/determiners, shared across language fragments and the studies
that consume the textbook-consensus B&C Table II metadata. The lexical
*entry* record is gone: a quantifier's lexical marking is now
`Syntax.Determiner.Quantifier` (`Syntax/Category/Determiner/Basic.lean`); these
enums survive only as the typological *labels* that record metadata
(force, monotonicity, weak/strong strength) reads off, and as the
parameter type of the GQT `gqtMeaning` operator.

## Main declarations

- `QForce` — quantificational force (universal, existential, …).
- `Monotonicity` — increasing / decreasing / non-monotone (typological label).
- `Strength` — weak / strong (Barwise & Cooper §4.3 Table II; weak
  determiners pass `there is/are`).
- `Adverb` — an adverb of quantification ([lewis-1975]), recorded with the
  force of the quantifier it lexicalizes.
-/


namespace Quantification.Lexicon


inductive QForce where
  | universal
  | existential
  | definite
  | negative
  | proportional
  deriving DecidableEq, Repr

inductive Monotonicity where
  | increasing
  | decreasing
  | nonMonotone
  deriving DecidableEq, Repr

/-- Weak/strong classification (B&C §4.3, Table II).
Weak determiners allow there-insertion: "There are some cats."
Strong determiners don't: "*There is every cat." -/
inductive Strength where
  | weak
  | strong
  deriving DecidableEq, Repr

/-- An adverb of quantification, a closed-class adverb quantifying over cases, situations or
occasions ([lewis-1975]): *always*, *usually*, *sometimes*, *never*. -/
structure Adverb where
  /-- The surface form. -/
  form : String
  /-- The force of the quantifier the adverb lexicalizes. -/
  force : QForce
  deriving DecidableEq, Repr

end Quantification.Lexicon

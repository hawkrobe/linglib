import Linglib.Features.InformationStructure
import Mathlib.Data.Set.Basic

/-!
# Focus interpretation

Set-based encoding of Rooth's focus interpretation principle (FIP).
Focus values are represented as `Set (Set W)`, matching Hamblin-style
question denotations; the anaphoric squiggle machinery lives in
`Semantics/Focus/Control.lean`.

## References

* [rooth-1992].
-/

open Features.InformationStructure

namespace Semantics.Focus.Interpretation

variable {W : Type*}

/-- Propositional focus value: a set of propositions over `W`. -/
abbrev PropFocusValue (W : Type*) := Set (Set W)

/-- Focus interpretation principle: the contextual contrast set `Γ` is a
subset of the focus semantic value. -/
def fip (gamma focusValue : Set (Set W)) : Prop :=
  gamma ⊆ focusValue

/-- Q-A congruence (strong): answer focus value equals question
denotation. -/
def qaCongruent (answerFocus question : PropFocusValue W) : Prop :=
  answerFocus = question

/-- Q-A congruence (weak): question denotation is a subset of the answer
focus value. -/
def qaCongruentWeak (answerFocus question : PropFocusValue W) : Prop :=
  question ⊆ answerFocus

end Semantics.Focus.Interpretation

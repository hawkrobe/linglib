/-
# Focus Interpretation (Rooth 1992)

Rooth's "A Theory of Focus Interpretation" introduces the Focus Interpretation
Principle (FIP) and the ~ operator to connect focus semantic values with context.

## Insight: Type Identity

Rooth's focus semantic value ⟦α⟧f has the same TYPE as Hamblin question denotations:
- `⟦α⟧f : (W → Bool) → Bool` (set of propositions)
- `QuestionDen W = (W → Bool) → Bool` (Hamblin question)

This grounds Q-A congruence: the focus value of an answer equals the question denotation.

## The ~ Operator

The squiggle operator (~) introduces a focus constraint via an anaphoric variable Γ:
- Γ is resolved to a salient set of alternatives from context
- FIP requires: Γ ⊆ ⟦α⟧f (the contrast set is a subset of focus alternatives)

## Four FIP Applications (Rooth §2)

1. Focusing adverbs (only, even) - association with focus
2. Contrast/parallelism - parallel focus triggers contrast presupposition
3. Scalar implicature - focus alternatives feed into SI computation
4. Q-A congruence - answer focus must match question

## References

- Rooth, M. (1992). A Theory of Focus Interpretation. Natural Language Semantics 1: 75-116.
- Hamblin, C. (1973). Questions in Montague English. Foundations of Language.
-/

import Linglib.Theories.TruthConditional.Sentence.Focus.InformationStructure
import Linglib.Theories.QuestionSemantics.Hamblin

open Theories.TruthConditional.Sentence.InformationStructure

namespace TruthConditional.Sentence.FocusInterpretation

-- Focus Semantic Values (Rooth 1985, 1992)

/-- Focus semantic value: a set of propositions (alternatives).
    Reuses the Alternatives structure from Core.InformationStructure.
    In Rooth's notation: ⟦α⟧f = {p | p is a focus alternative of α} -/
abbrev FocusValue (α : Type) := Alternatives α

/-- Propositional focus value: set of propositions.
    Type: <<s,t>,t> - same as Hamblin questions! -/
abbrev PropFocusValue (W : Type*) := (W → Bool) → Bool

-- The ~ Operator (Squiggle)

/-- The ~ operator introduces a focus constraint via anaphor Γ.

    Rooth (1992) §2: "α ~ Γ" where:
    - α is an expression with focus marking
    - Γ is an anaphoric variable resolved to a contextual set of alternatives
    - FIP requires: Γ ⊆ ⟦α⟧f -/
structure Squiggle (W : Type*) where
  /-- The contrasting set Γ (anaphor to context) -/
  contrastSet : (W → Bool) → Bool

/-- Focus Interpretation Principle (FIP):
    The contextual contrast set Γ must be a subset of the focus semantic value.

    Rooth (1992) §2: "Γ ⊆ ⟦α⟧f" -/
def fip {W : Type*} (gamma : (W → Bool) → Bool) (focusValue : (W → Bool) → Bool) : Prop :=
  ∀ p, gamma p → focusValue p

-- Grounding: Hamblin Questions = Focus Semantic Values

/-- Grounding theorem: Hamblin question denotations have the same type as
    propositional focus semantic values.

    This is the foundation of Q-A congruence: the focus value of an answer
    should equal (or be a superset of) the question denotation. -/
theorem hamblin_is_focus_type (W : Type*) :
    QuestionSemantics.Hamblin.QuestionDen W = ((W → Bool) → Bool) := rfl

-- Question-Answer Congruence

/-- Q-A Congruence: An answer is congruent to a question iff the focus
    semantic value of the answer equals the question denotation.

    Rooth (1992) §4: Focus on the answer must match the wh-position in the question.

    Example:
    - Q: "Who ate the beans?" = {λw. ate(x, beans, w) | x ∈ D}
    - A: "FRED ate the beans" has ⟦A⟧f = {λw. ate(x, beans, w) | x ∈ D}
    - Congruent iff ⟦A⟧f = ⟦Q⟧ -/
def qaCongruent {W : Type*} (answerFocus : PropFocusValue W)
    (question : QuestionSemantics.Hamblin.QuestionDen W) : Prop :=
  answerFocus = question

/-- Weaker Q-A congruence: question alternatives are a subset of answer focus.
    This handles cases where the answer may introduce additional alternatives. -/
def qaCongruentWeak {W : Type*} (answerFocus : PropFocusValue W)
    (question : QuestionSemantics.Hamblin.QuestionDen W) : Prop :=
  ∀ p, question p → answerFocus p

-- FIP Applications (Rooth §2)

/-- Application type for the Focus Interpretation Principle -/
inductive FIPApplication where
  /-- Focusing adverbs: only, even, also -/
  | focusingAdverb
  /-- Contrast/parallelism in discourse -/
  | contrast
  /-- Scalar implicature computation -/
  | scalarImplicature
  /-- Question-answer congruence -/
  | qaCongruence
  deriving DecidableEq, Repr, BEq

/-- Description of each FIP application -/
def FIPApplication.description : FIPApplication → String
  | .focusingAdverb => "Focus-sensitive particles (only, even, also) associate with focus"
  | .contrast => "Parallel focus in discourse triggers contrast presupposition"
  | .scalarImplicature => "Focus alternatives feed into scalar implicature computation"
  | .qaCongruence => "Answer focus must match question (see Questions/FocusAnswer.lean)"

-- Connection to Additive Particles

/-!
## Additive Particles and FIP

Rooth (1992) §2.2 analyzes "too" via FIP:

"Mary read Lear, and she read Macbeth too"
- Focus: MACBETH
- ⟦Macbeth⟧f = {Lear, Macbeth, Hamlet, ...} (works of Shakespeare)
- Antecedent "Lear" must be in ⟦Macbeth⟧f ✓
- FIP: The antecedent is in the focus alternatives

See:
- `Phenomena/AdditiveParticles/Data.lean` for empirical data
- `Theories/Montague/Particle/Additive.lean` for semantic analysis
-/

end TruthConditional.Sentence.FocusInterpretation

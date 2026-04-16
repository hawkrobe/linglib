/-
# Focus Interpretation @cite{rooth-1992}

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

-/

import Linglib.Core.InformationStructure
import Linglib.Theories.Semantics.Questions.Denotation.Hamblin

open Core.InformationStructure

namespace Semantics.FocusInterpretation

-- Focus Semantic Values (@cite{rooth-1985}, 1992)

/-- Propositional focus value: set of propositions.
    Type: <<s,t>,t> - same as Hamblin questions! -/
abbrev PropFocusValue (W : Type*) := (W → Bool) → Bool

-- The ~ Operator (Squiggle)

/-- The ~ operator introduces a focus constraint via anaphor Γ.

    @cite{rooth-1992} §2: "α ~ Γ" where:
    - α is an expression with focus marking
    - Γ is an anaphoric variable resolved to a contextual set of alternatives
    - FIP requires: Γ ⊆ ⟦α⟧f -/
structure Squiggle (W : Type*) where
  /-- The contrasting set Γ (anaphor to context) -/
  contrastSet : (W → Bool) → Bool

/-- Focus Interpretation Principle (FIP):
    The contextual contrast set Γ must be a subset of the focus semantic value.

    @cite{rooth-1992} §2: "Γ ⊆ ⟦α⟧f" -/
def fip {W : Type*} (gamma : (W → Bool) → Bool) (focusValue : (W → Bool) → Bool) : Prop :=
  ∀ p, gamma p → focusValue p

-- Grounding: Hamblin Questions = Focus Semantic Values

/-- Grounding theorem: Hamblin question denotations have the same type as
    propositional focus semantic values.

    This is the foundation of Q-A congruence: the focus value of an answer
    should equal (or be a superset) the question denotation. -/
theorem hamblin_is_focus_type (W : Type*) :
    Semantics.Questions.Hamblin.QuestionDen W = ((W → Bool) → Bool) := rfl

-- Question-Answer Congruence

/-- Q-A Congruence: An answer is congruent to a question iff the focus
    semantic value of the answer equals the question denotation.

    @cite{rooth-1992} §4: Focus on the answer must match the wh-position in the question.

    Example:
    - Q: "Who ate the beans?" = {λw. ate(x, beans, w) | x ∈ D}
    - A: "FRED ate the beans" has ⟦A⟧f = {λw. ate(x, beans, w) | x ∈ D}
    - Congruent iff ⟦A⟧f = ⟦Q⟧ -/
def qaCongruent {W : Type*} (answerFocus : PropFocusValue W)
    (question : Semantics.Questions.Hamblin.QuestionDen W) : Prop :=
  answerFocus = question

/-- Weaker Q-A congruence: question alternatives are a subset of answer focus.
    This handles cases where the answer may introduce additional alternatives. -/
def qaCongruentWeak {W : Type*} (answerFocus : PropFocusValue W)
    (question : Semantics.Questions.Hamblin.QuestionDen W) : Prop :=
  ∀ p, question p → answerFocus p

-- FIP Applications (Rooth §2)
-- FIPApplication is defined in Core.InformationStructure (opened above)

/-- Description of each FIP application -/
def FIPApplication.description : FIPApplication → String
  | .focusingAdverb => "Focus-sensitive particles (only, even, also) associate with focus"
  | .contrast => "Parallel focus in discourse triggers contrast presupposition"
  | .scalarImplicature => "Focus alternatives feed into scalar implicature computation"
  | .qaCongruence => "Answer focus must match question (see Questions/FocusAnswer.lean)"

-- ============================================================================
-- Focus Resolution (Extended ~ Semantics)
-- ============================================================================

/-!
## Full ~ Operator: Focus Resolution

@cite{rooth-1992} §2: α ~ introduces an anaphoric variable C (the
comparison class / contrast set) constrained by TWO conditions:

1. **FIP**: C ⊆ ⟦α⟧f — every proposition in C is a focus alternative
2. **Ordinary inclusion**: ⟦α⟧o ∈ C — the ordinary value is in C

The existing `fip` function captures constraint 1 alone. `FocusResolution`
bundles both constraints, making the full ~ semantics explicit.

This is the entry point for the compositional chain that derives TSP:
~ resolves C → degree predicate uses C → significance falls out.
See `Focus/Sensitivity.lean` for the downstream derivation.
-/

/-- The full ~ operator resolves focus alternatives to a comparison class C.

    Bundles @cite{rooth-1992}'s two constraints:
    1. C ⊆ ⟦α⟧f (FIP — comparison class bounded by focus alternatives)
    2. ⟦α⟧o ∈ C (ordinary value is in the comparison class)

    The comparison class is extensional (`List (W → Bool)`) for compatibility
    with `Attitudes.Preferential.QuestionDen`. -/
structure FocusResolution (W : Type*) where
  /-- ⟦α⟧o — the ordinary semantic value of the focused constituent -/
  ordinary : W → Bool
  /-- ⟦α⟧f — the focus semantic value (set of alternative propositions) -/
  focusValue : PropFocusValue W
  /-- C — the comparison class, resolved from context -/
  comparisonClass : List (W → Bool)
  /-- FIP: C ⊆ ⟦α⟧f — every proposition in C is a focus alternative -/
  fip_subset : ∀ p ∈ comparisonClass, focusValue p
  /-- ⟦α⟧o ∈ C — the ordinary value is in the comparison class -/
  ordinary_in_C : ordinary ∈ comparisonClass

-- ============================================================================
-- Clause-Embedding Predicates with Focus (@cite{ozyildiz-etal-2025})
-- ============================================================================

/-- A clause-embedding predicate with explicit access to focus alternatives.

    Takes: agent, ordinary proposition, focus alternatives, world → truth value.

    Non-focus-sensitive predicates (believe, know) ignore the focus alternatives.
    Focus-sensitive predicates (want, be glad, be surprised) use them to
    determine the comparison class for degree semantics.

    @cite{ozyildiz-etal-2025} def 2/58. -/
abbrev ClauseEmbedPred (W E : Type*) := E → (W → Bool) → PropFocusValue W → W → Bool

/-- A clause-embedding predicate V is **focus-sensitive** iff its truth value
    can depend on the focus alternatives, not just the ordinary proposition.

    @cite{ozyildiz-etal-2025} def 2/58: there exist context, agent, proposition,
    and two different focus-alternative sets such that V yields different truth
    values. -/
def IsFocusSensitive {W E : Type*} (V : ClauseEmbedPred W E) : Prop :=
  ∃ (x : E) (p : W → Bool) (f₁ f₂ : PropFocusValue W) (w : W),
    V x p f₁ w ≠ V x p f₂ w

/-- A predicate is **not** focus-sensitive iff it ignores focus alternatives
    entirely. -/
def IsNotFocusSensitive {W E : Type*} (V : ClauseEmbedPred W E) : Prop :=
  ∀ (x : E) (p : W → Bool) (f₁ f₂ : PropFocusValue W) (w : W),
    V x p f₁ w = V x p f₂ w

theorem not_fs_iff_ignores_focus {W E : Type*} (V : ClauseEmbedPred W E) :
    IsNotFocusSensitive V ↔ ¬ IsFocusSensitive V := by
  constructor
  · intro h ⟨x, p, f₁, f₂, w, hne⟩; exact hne (h x p f₁ f₂ w)
  · intro h x p f₁ f₂ w
    by_contra hne
    exact h ⟨x, p, f₁, f₂, w, hne⟩

/-- Lift a non-focus-sensitive predicate to the `ClauseEmbedPred` type
    by ignoring focus alternatives. -/
def liftNonFS {W E : Type*} (V : E → (W → Bool) → W → Bool) : ClauseEmbedPred W E :=
  λ x p _f w => V x p w

/-- Any lifted non-focus-sensitive predicate is indeed not focus-sensitive. -/
theorem liftNonFS_not_fs {W E : Type*} (V : E → (W → Bool) → W → Bool) :
    IsNotFocusSensitive (liftNonFS V) := by
  intro _ _ _ _ _; rfl

-- Connection to Additive Particles

/-!
## Additive Particles and FIP

@cite{rooth-1992} §2.2 analyzes "too" via FIP: @cite{rooth-1985}

"Mary read Lear, and she read Macbeth too"
- Focus: MACBETH
- ⟦Macbeth⟧f = {Lear, Macbeth, Hamlet,...} (works of Shakespeare)
- Antecedent "Lear" must be in ⟦Macbeth⟧f ✓
- FIP: The antecedent is in the focus alternatives

See:
- `Phenomena/AdditiveParticles/Data.lean` for empirical data
- `Theories/Semantics/Focus/Particles.lean` for semantic analysis
-/

end Semantics.FocusInterpretation

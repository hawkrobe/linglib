import Linglib.Features.InformationStructure
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Tauto

/-!
# Focus interpretation

Set-based encoding of Rooth's focus interpretation principle (FIP) and
the squiggle (~) operator. Focus values are represented as `Set (Set W)`,
matching Hamblin-style question denotations.

## Main definitions

* `PropFocusValue W`: propositional focus value `Set (Set W)`.
* `Squiggle W`: a squiggle anaphor carrying its contrast set Γ.
* `fip`: Rooth's focus interpretation principle (Γ ⊆ ⟦α⟧f).
* `qaCongruent` / `qaCongruentWeak`: Q-A congruence as set-equality
  and as the weaker subset relation.
* `FocusResolution W`: bundles FIP with the ordinary-value-in-class
  constraint.
* `ClauseEmbedPred W E`: clause-embedding predicate with explicit
  access to focus alternatives.
* `IsFocusSensitive`, `IsNotFocusSensitive`: focus sensitivity of a
  clause-embedding predicate, with a `liftNonFS` lift for the negative
  case.

## References

* @cite{rooth-1992}, @cite{ozyildiz-etal-2025}.
-/

open Features.InformationStructure

namespace Semantics.Focus.Interpretation

variable {W E : Type*}

/-- Propositional focus value: a set of propositions over `W`. -/
abbrev PropFocusValue (W : Type*) := Set (Set W)

/-- The ~ operator introduces a focus constraint via the anaphoric
contrast set `Γ`. -/
structure Squiggle (W : Type*) where
  /-- The contrast set `Γ`, resolved from context. -/
  contrastSet : Set (Set W)

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

/-- Short label for each `FIPApplication` case. -/
def FIPApplication.description : FIPApplication → String
  | .focusingAdverb => "Focus-sensitive particles (only, even, also) associate with focus"
  | .contrast => "Parallel focus in discourse triggers contrast presupposition"
  | .scalarImplicature => "Focus alternatives feed into scalar implicature computation"
  | .qaCongruence => "Answer focus must match question (see Questions/FocusAnswer.lean)"

/-- The full ~ operator: resolves focus alternatives to a comparison
class `C` constrained by FIP (`C ⊆ ⟦α⟧f`) and ordinary-inclusion
(`⟦α⟧o ∈ C`). -/
structure FocusResolution (W : Type*) where
  /-- The ordinary semantic value `⟦α⟧o`. -/
  ordinary : Set W
  /-- The focus semantic value `⟦α⟧f`. -/
  focusValue : PropFocusValue W
  /-- The comparison class `C`, resolved from context. -/
  comparisonClass : Set (Set W)
  /-- FIP: `C ⊆ ⟦α⟧f`. -/
  fip_subset : comparisonClass ⊆ focusValue
  /-- The ordinary value lies in the comparison class. -/
  ordinary_in_C : ordinary ∈ comparisonClass

/-- Clause-embedding predicate with explicit access to focus
alternatives: agent → ordinary proposition → focus alternatives → world
predicate. @cite{ozyildiz-etal-2025}. -/
abbrev ClauseEmbedPred (W E : Type*) := E → Set W → PropFocusValue W → Set W

/-- A clause-embedding predicate is focus-sensitive when its truth
depends on the focus alternatives, not just the ordinary proposition. -/
def IsFocusSensitive (V : ClauseEmbedPred W E) : Prop :=
  ∃ (x : E) (p : Set W) (f₁ f₂ : PropFocusValue W) (w : W),
    (w ∈ V x p f₁) ≠ (w ∈ V x p f₂)

/-- A clause-embedding predicate ignores focus alternatives entirely. -/
def IsNotFocusSensitive (V : ClauseEmbedPred W E) : Prop :=
  ∀ (x : E) (p : Set W) (f₁ f₂ : PropFocusValue W),
    V x p f₁ = V x p f₂

theorem not_fs_iff_ignores_focus (V : ClauseEmbedPred W E) :
    IsNotFocusSensitive V ↔ ¬ IsFocusSensitive V := by
  constructor
  · intro h ⟨x, p, f₁, f₂, w, hne⟩; exact hne (by rw [h x p f₁ f₂])
  · intro h x p f₁ f₂
    ext w
    by_contra hne
    exact h ⟨x, p, f₁, f₂, w, by tauto⟩

/-- Lift a focus-agnostic predicate to a `ClauseEmbedPred` by ignoring
the focus alternatives. -/
def liftNonFS (V : E → Set W → Set W) : ClauseEmbedPred W E :=
  λ x p _f => V x p

theorem liftNonFS_not_fs (V : E → Set W → Set W) :
    IsNotFocusSensitive (liftNonFS V) := by
  intro _ _ _ _; rfl

end Semantics.Focus.Interpretation

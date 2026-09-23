module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Tactic.DeriveFintype

/-!
# Sentence polarity

Binary sentence polarity: positive (affirmative) vs negative. Polarities compose as the group of
order two, a negation cancelling a negation, and act on propositions, the negative polarity by
complement: `SentencePolarity.negative • p = pᶜ`.

Used across phenomena involving polarity-sensitive behavior: answers to polar questions,
multiplicity inferences, homogeneity gaps, scalar implicatures, etc.

Note: This is distinct from other polarity-like distinctions in the library:
- `UD.Polarity`: the morphological feature (`.Pos`/`.Neg`)
- `NaturalLogic.ContextPolarity`: monotonicity direction (`.upward`/`.downward`)
- `Presupposition.Aboutness.EventSentence.polarity`: polarity of the event claim
- `Degree.Polarity`: the polarity of an antonym, the same group of order two as `ℤˣ`
-/

@[expose] public section

/--
Sentence polarity: whether a sentence is affirmative or negated.
-/
inductive SentencePolarity where
  | positive
  | negative
  deriving Repr, DecidableEq, Inhabited, Fintype

namespace SentencePolarity

instance : One SentencePolarity where
  one := positive

/-- Composition of polarities: two negations cancel. -/
instance : Mul SentencePolarity where
  mul
    | positive, s => s
    | negative, positive => negative
    | negative, negative => positive

/-- The polarities form the group of order two, each polarity its own inverse. -/
instance : CommGroup SentencePolarity where
  inv := id
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_comm := by decide

@[simp] theorem one_eq_positive : (1 : SentencePolarity) = positive := rfl

@[simp] theorem inv_eq_self (s : SentencePolarity) : s⁻¹ = s := rfl

@[simp] theorem mul_self (s : SentencePolarity) : s * s = positive := by cases s <;> rfl

@[simp] theorem positive_mul (s : SentencePolarity) : positive * s = s := rfl

@[simp] theorem mul_positive (s : SentencePolarity) : s * positive = s := mul_one s

variable {α : Type*}

/-- A polarity acts on a proposition: the positive one leaves it, the negative one takes its
complement. -/
instance : MulAction SentencePolarity (Set α) where
  smul
    | positive, p => p
    | negative, p => pᶜ
  one_smul _ := rfl
  mul_smul s t p := by cases s <;> cases t <;> first | rfl | exact (compl_compl p).symm

@[simp] theorem positive_smul (p : Set α) : positive • p = p := rfl

@[simp] theorem negative_smul (p : Set α) : negative • p = pᶜ := rfl

end SentencePolarity

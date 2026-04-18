/-
Semantic entailment over a finite world semantics.
A |= B iff every model satisfying A also satisfies B.
Reference: @cite{van-benthem-1986}, @cite{ladusaw-1980}, @cite{barwise-cooper-1981}.
-/

import Linglib.Core.Semantics.Proposition

namespace Semantics.Entailment

open Core.Proposition (Prop')

section FiniteWorldSemantics

/-- A small finite set of worlds for decidable reasoning. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr

def allWorlds : List World := [.w0, .w1, .w2, .w3]

instance : Fintype World where
  elems := {.w0, .w1, .w2, .w3}
  complete := fun w => by cases w <;> decide

end FiniteWorldSemantics

section Entailment

/-- Semantic entailment: p entails q iff q is true whenever p is true. -/
def entails (p q : Prop' World) : Prop :=
  ∀ w, p w → q w

instance (p q : Prop' World) [DecidablePred p] [DecidablePred q] :
    Decidable (entails p q) :=
  inferInstanceAs (Decidable (∀ w, p w → q w))

end Entailment

section PropositionalOperations

/-- Negation. -/
def pnot (p : Prop' World) : Prop' World := Core.Proposition.Classical.pnot World p

/-- Conjunction. -/
def pand (p q : Prop' World) : Prop' World := Core.Proposition.Classical.pand World p q

/-- Disjunction. -/
def por (p q : Prop' World) : Prop' World := Core.Proposition.Classical.por World p q

instance (p : Prop' World) [DecidablePred p] : DecidablePred (pnot p) :=
  fun w => inferInstanceAs (Decidable (¬ p w))

instance (p q : Prop' World) [DecidablePred p] [DecidablePred q] :
    DecidablePred (pand p q) :=
  fun w => inferInstanceAs (Decidable (p w ∧ q w))

instance (p q : Prop' World) [DecidablePred p] [DecidablePred q] :
    DecidablePred (por p q) :=
  fun w => inferInstanceAs (Decidable (p w ∨ q w))

/-- Negation reverses entailment. -/
theorem pnot_reverses_entailment (p q : Prop' World)
    (h : ∀ w, p w → q w) :
    ∀ w, pnot q w → pnot p w := by
  intro w hnq hp
  exact hnq (h w hp)

end PropositionalOperations

section TestPropositions

/-- Proposition true only in w0. -/
def p0 : Prop' World := λ w => w = .w0

/-- Proposition true in w0 and w1. -/
def p01 : Prop' World := λ w => w = .w0 ∨ w = .w1

/-- Proposition true in w0, w1, w2. -/
def p012 : Prop' World := λ w => w = .w0 ∨ w = .w1 ∨ w = .w2

/-- Proposition true everywhere. -/
def pAll : Prop' World := λ _ => True

/-- Proposition false everywhere. -/
def pNone : Prop' World := λ _ => False

instance : DecidablePred p0 := fun w => by unfold p0; infer_instance
instance : DecidablePred p01 := fun w => by unfold p01; infer_instance
instance : DecidablePred p012 := fun w => by unfold p012; infer_instance
instance : DecidablePred pAll := fun _ => isTrue trivial
instance : DecidablePred pNone := fun _ => isFalse not_false

/-- Test cases for monotonicity: pairs where first entails second. -/
def testCases : List (Prop' World × Prop' World) :=
  [(p0, p01), (p01, p012), (p012, pAll), (p0, pAll)]

/-- p0 entails p01. -/
theorem p0_entails_p01 : entails p0 p01 := by decide

/-- p01 entails p012. -/
theorem p01_entails_p012 : entails p01 p012 := by decide

end TestPropositions

end Semantics.Entailment

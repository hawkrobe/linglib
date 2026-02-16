/-
Semantic entailment over a finite world semantics.
A |= B iff every model satisfying A also satisfies B.
Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981).
-/

import Linglib.Core.Proposition

namespace Semantics.Entailment

section FiniteWorldSemantics

/-- A small finite set of worlds for decidable reasoning. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr

def allWorlds : List World := [.w0, .w1, .w2, .w3]

end FiniteWorldSemantics

section Entailment

/-- Semantic entailment: p entails q iff q is true whenever p is true. -/
def entails (p q : BProp World) : Bool :=
  Core.Proposition.Decidable.entails World allWorlds p q

end Entailment

section PropositionalOperations

/-- Negation: (pnot p) w = !(p w). -/
def pnot (p : BProp World) : BProp World := Core.Proposition.Decidable.pnot World p

/-- Conjunction: (pand p q) w = p w && q w. -/
def pand (p q : BProp World) : BProp World := Core.Proposition.Decidable.pand World p q

/-- Disjunction: (por p q) w = p w || q w. -/
def por (p q : BProp World) : BProp World := Core.Proposition.Decidable.por World p q

/-- Negation reverses entailment, specialized to `World`. -/
theorem pnot_reverses_entailment (p q : BProp World)
    (h : ∀ w, p w = true → q w = true) :
    ∀ w, pnot q w = true → pnot p w = true :=
  Core.Proposition.Decidable.pnot_reverses_entailment p q h

end PropositionalOperations

section TestPropositions

/-- Proposition true only in w0. -/
def p0 : BProp World := λ w => w == .w0

/-- Proposition true in w0 and w1. -/
def p01 : BProp World := λ w => w == .w0 || w == .w1

/-- Proposition true in w0, w1, w2. -/
def p012 : BProp World := λ w => w == .w0 || w == .w1 || w == .w2

/-- Proposition true everywhere. -/
def pAll : BProp World := λ _ => true

/-- Proposition false everywhere. -/
def pNone : BProp World := λ _ => false

/-- Test cases for monotonicity: pairs where first entails second. -/
def testCases : List (BProp World × BProp World) :=
  [(p0, p01), (p01, p012), (p012, pAll), (p0, pAll)]

/-- p0 entails p01. -/
theorem p0_entails_p01 : entails p0 p01 = true := by native_decide

/-- p01 entails p012. -/
theorem p01_entails_p012 : entails p01 p012 = true := by native_decide

end TestPropositions

end Semantics.Entailment

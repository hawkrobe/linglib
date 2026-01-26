/-
# Semantic Entailment: Core Definitions

This module provides the core definitions for entailment over a finite world semantics.

## Key Concepts

**Entailment**: A ⊨ B iff every model satisfying A also satisfies B

Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981)
-/

namespace Montague.Entailment

-- ============================================================================
-- Finite World Semantics
-- ============================================================================

/-- A small finite set of worlds for decidable reasoning -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr

def allWorlds : List World := [.w0, .w1, .w2, .w3]

/-- A proposition is a function from worlds to truth values -/
abbrev Prop' := World → Bool

-- ============================================================================
-- Entailment (Decidable Version)
-- ============================================================================

/-- Semantic entailment: p entails q iff q is true whenever p is true -/
def entails (p q : Prop') : Bool :=
  allWorlds.all λ w => !p w || q w

-- ============================================================================
-- Propositional Operations
-- ============================================================================

def pnot (p : Prop') : Prop' := λ w => !p w
def pand (p q : Prop') : Prop' := λ w => p w && q w
def por (p q : Prop') : Prop' := λ w => p w || q w

-- ============================================================================
-- Concrete Test Propositions
-- ============================================================================

/-- Proposition true only in w0 -/
def p0 : Prop' := λ w => w == .w0

/-- Proposition true in w0 and w1 -/
def p01 : Prop' := λ w => w == .w0 || w == .w1

/-- Proposition true in w0, w1, w2 -/
def p012 : Prop' := λ w => w == .w0 || w == .w1 || w == .w2

/-- Proposition true everywhere -/
def pAll : Prop' := λ _ => true

/-- Proposition false everywhere -/
def pNone : Prop' := λ _ => false

-- Entailment chain: p0 ⊨ p01 ⊨ p012 ⊨ pAll
-- (smaller sets entail larger sets)

/-- Test cases for monotonicity: pairs where first entails second -/
def testCases : List (Prop' × Prop') :=
  [(p0, p01), (p01, p012), (p012, pAll), (p0, pAll)]

-- ============================================================================
-- Basic Entailment Theorems
-- ============================================================================

/-- p0 entails p01 -/
theorem p0_entails_p01 : entails p0 p01 = true := by native_decide

/-- p01 entails p012 -/
theorem p01_entails_p012 : entails p01 p012 = true := by native_decide

end Montague.Entailment

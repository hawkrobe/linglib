/-
# Semantic Monotonicity

This module defines upward and downward entailing contexts and proves
monotonicity properties of various operators.

## Key Concepts

**Monotonicity**: A function f on propositions is:
  - Upward Entailing (UE): A ⊨ B → f(A) ⊨ f(B)
  - Downward Entailing (DE): A ⊨ B → f(B) ⊨ f(A)

Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981)
-/

import Linglib.Theories.Montague.Sentence.Entailment.Basic

namespace Montague.Sentence.Entailment.Monotonicity

open Montague.Sentence.Entailment

-- ============================================================================
-- Monotonicity (Decidable Versions)
-- ============================================================================

/-- Check if f is upward entailing on given test cases -/
def isUpwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f p) (f q)

/-- Check if f is downward entailing on given test cases -/
def isDownwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f q) (f p)

-- ============================================================================
-- Monotonicity Theorems
-- ============================================================================

/--
**Theorem: Negation is Downward Entailing**

If P ⊨ Q, then ¬Q ⊨ ¬P

Test: p0 ⊨ p01, so ¬p01 ⊨ ¬p0
-/
theorem negation_is_DE : isDownwardEntailing pnot testCases = true := by
  native_decide

/--
**Concrete example: Negation reverses entailment**

p0 ⊨ p01 (true in {w0} entails true in {w0,w1})
¬p01 ⊨ ¬p0 (false in {w0,w1} entails false in {w0})
-/
theorem negation_reverses_example :
    entails p0 p01 = true ∧
    entails (pnot p01) (pnot p0) = true := by
  native_decide

/--
**Theorem: Conjunction (second arg) is Upward Entailing**

If P ⊨ Q, then (R ∧ P) ⊨ (R ∧ Q)
-/
theorem conjunction_second_UE : isUpwardEntailing (pand p01) testCases = true := by
  native_decide

/--
**Theorem: Disjunction (second arg) is Upward Entailing**

If P ⊨ Q, then (R ∨ P) ⊨ (R ∨ Q)
-/
theorem disjunction_second_UE : isUpwardEntailing (por p01) testCases = true := by
  native_decide

-- ============================================================================
-- Quantifier Semantics
-- ============================================================================

/-- "Every A is B" = ∀x. A(x) → B(x) -/
def every (a b : World → Bool) : Bool :=
  allWorlds.all λ x => !a x || b x

/-- "Some A is B" = ∃x. A(x) ∧ B(x) -/
def some' (a b : World → Bool) : Bool :=
  allWorlds.any λ x => a x && b x

/-- "No A is B" = ∀x. A(x) → ¬B(x) -/
def no (a b : World → Bool) : Bool :=
  allWorlds.all λ x => !a x || !b x

-- Fixed restrictor for testing
def fixedRestr : Prop' := p01  -- "students" = {w0, w1}

/-- "Every student" as a function of scope -/
def every_scope : Prop' → Prop' :=
  λ scope => λ _ => every fixedRestr scope

/-- "Some student" as a function of scope -/
def some_scope : Prop' → Prop' :=
  λ scope => λ _ => some' fixedRestr scope

/-- "No student" as a function of scope -/
def no_scope : Prop' → Prop' :=
  λ scope => λ _ => no fixedRestr scope

/--
**Theorem: "Every" is UE in scope**

If P ⊨ Q, then "Every student P" ⊨ "Every student Q"
-/
theorem every_scope_UE : isUpwardEntailing every_scope testCases = true := by
  native_decide

/--
**Theorem: "Some" is UE in scope**

If P ⊨ Q, then "Some student P" ⊨ "Some student Q"
-/
theorem some_scope_UE : isUpwardEntailing some_scope testCases = true := by
  native_decide

/--
**Theorem: "No" is DE in scope**

If P ⊨ Q, then "No student Q" ⊨ "No student P"

This is why "no" blocks scalar implicatures!
-/
theorem no_scope_DE : isDownwardEntailing no_scope testCases = true := by
  native_decide

-- ============================================================================
-- "Every" Restrictor is DE
-- ============================================================================

/-- Fixed scope for testing restrictor monotonicity -/
def fixedScope : Prop' := p012  -- "smokes" = {w0, w1, w2}

/-- "Every ___ smokes" as a function of restrictor -/
def every_restr : Prop' → Prop' :=
  λ restr => λ _ => every restr fixedScope

/--
**Theorem: "Every" is DE in restrictor**

If P ⊨ Q, then "Every Q smokes" ⊨ "Every P smokes"

Example: dogs ⊨ mammals, so "every mammal smokes" ⊨ "every dog smokes"
-/
theorem every_restr_DE : isDownwardEntailing every_restr testCases = true := by
  native_decide

/--
**Key Insight: DE contexts reverse scalar strength**

In UE: all ⊢ some (all is stronger, "some" implicates "not all")
In DE: some ⊢ all (some is stronger, no "not all" implicature)
-/
theorem de_reverses_strength :
    -- In UE context (identity), p0 ⊢ p01 means p0 is stronger
    entails p0 p01 = true ∧
    -- Under negation (DE), the relationship reverses
    entails (pnot p01) (pnot p0) = true := by
  native_decide

end Montague.Sentence.Entailment.Monotonicity

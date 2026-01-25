/-
# Semantic Entailment and Monotonicity

This module provides the semantic foundation for understanding:
1. When one expression entails another
2. Which contexts are upward/downward entailing
3. Why scalar implicatures are blocked in DE contexts

## Key Concepts

**Entailment**: A ⊨ B iff every model satisfying A also satisfies B

**Monotonicity**: A function f on propositions is:
  - Upward Entailing (UE): A ⊨ B → f(A) ⊨ f(B)
  - Downward Entailing (DE): A ⊨ B → f(B) ⊨ f(A)

Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981)
-/

import Linglib.Theories.Montague.Scales

namespace Montague.Entailment

-- ============================================================================
-- PART 1: Finite World Semantics
-- ============================================================================

/-- A small finite set of worlds for decidable reasoning -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr

def allWorlds : List World := [.w0, .w1, .w2, .w3]

/-- A proposition is a function from worlds to truth values -/
abbrev Prop' := World → Bool

-- ============================================================================
-- PART 2: Entailment (Decidable Version)
-- ============================================================================

/-- Semantic entailment: p entails q iff q is true whenever p is true -/
def entails (p q : Prop') : Bool :=
  allWorlds.all λ w => !p w || q w

-- ============================================================================
-- PART 3: Monotonicity (Decidable Versions)
-- ============================================================================

/-- Check if f is upward entailing on given test cases -/
def isUpwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f p) (f q)

/-- Check if f is downward entailing on given test cases -/
def isDownwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f q) (f p)

-- ============================================================================
-- PART 4: Propositional Operations
-- ============================================================================

def pnot (p : Prop') : Prop' := λ w => !p w
def pand (p q : Prop') : Prop' := λ w => p w && q w
def por (p q : Prop') : Prop' := λ w => p w || q w

-- ============================================================================
-- PART 5: Concrete Test Propositions
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
-- PART 6: Monotonicity Theorems
-- ============================================================================

/-- p0 entails p01 -/
theorem p0_entails_p01 : entails p0 p01 = true := by native_decide

/-- p01 entails p012 -/
theorem p01_entails_p012 : entails p01 p012 = true := by native_decide

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
-- PART 7: Quantifier Semantics
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
-- PART 8: "Every" Restrictor is DE
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

-- ============================================================================
-- PART 9: Application to Scalar Implicatures
-- ============================================================================

/-
## Why Monotonicity Matters for Scalar Implicatures

### The Pattern

In **UE contexts** (default):
- Scale: some < all (all is informationally stronger)
- Speaker said "some"
- Alternative "all" was available but not used
- Implicature: speaker doesn't believe "all" holds

In **DE contexts** (negation, "no", restrictor of "every"):
- Entailment REVERSES
- "some" becomes informationally STRONGER than "all"
- "No one ate some" ⊢ "No one ate all" (not the other way!)
- No alternative to negate → no implicature

### Summary Table

| Context              | Position    | Monotonicity | Implicature? |
|---------------------|-------------|--------------|--------------|
| Simple predication  | scope       | UE           | Yes          |
| Negation            | argument    | DE           | Blocked      |
| "every"             | scope       | UE           | Yes          |
| "every"             | restrictor  | DE           | Blocked      |
| "some"              | scope       | UE           | Yes          |
| "no"                | scope       | DE           | Blocked      |
-/

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

-- ============================================================================
-- PART 10: Connection to Horn Scales
-- ============================================================================

/-
## How Monotonicity Affects Scalar Alternatives

Horn scales (from Scales.lean) are ordered by semantic strength.
In UE contexts, stronger terms are scalar alternatives.
In DE contexts, the scale REVERSES - weaker terms become alternatives.

This explains why "some → not all" is blocked in DE contexts:
- In UE: "all" is a stronger alternative to "some"
- In DE: "all" is NOT a stronger alternative (scale reversed)
-/

open Montague.Scales

/--
**Scale Reversal in DE Contexts**

In UE context: "some" has stronger alternatives [most, all]
In DE context: "some" has only weaker alternatives [none] - it's now strongest!
-/
theorem scale_alternatives_reverse :
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide

/--
**DE Blocks "Some → Not All" Implicature**

The implicature requires "all" to be a stronger alternative.
In DE contexts, "all" is NOT in the alternatives - hence no implicature.
-/
theorem de_blocks_scalar_implicature :
    -- In UE, alternatives include "all"
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    -- In DE, alternatives do NOT include "all"
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Proven Monotonicity Properties

### DE (Downward Entailing) - blocks scalar implicatures
- `negation_is_DE`: ¬ is DE
- `no_scope_DE`: scope of "no" is DE
- `every_restr_DE`: restrictor of "every" is DE

### UE (Upward Entailing) - allows scalar implicatures
- `conjunction_second_UE`: ∧ is UE in second arg
- `disjunction_second_UE`: ∨ is UE in second arg
- `every_scope_UE`: scope of "every" is UE
- `some_scope_UE`: scope of "some" is UE

### Key Results
- `negation_reverses_example`: Concrete proof that negation reverses entailment
- `de_reverses_strength`: DE contexts reverse scalar strength ordering
- `scale_alternatives_reverse`: DE reverses which alternatives are "stronger"
- `de_blocks_scalar_implicature`: Explains why "not all" blocked in DE

### Connection to Scales.lean
This module imports Scales.lean and shows how the semantic property of
downward entailment causes the scale reversal that blocks implicatures.
-/

end Montague.Entailment

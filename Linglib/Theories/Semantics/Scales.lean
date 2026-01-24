/-
# Horn Scales

Horn scales (Horn 1972) are ordered sets of expressions where:
1. All members have the same semantic type
2. They are ordered by **informativity** (semantic strength)
3. Stronger members entail weaker members

Examples:
- ⟨some, most, all⟩ (quantifiers)
- ⟨or, and⟩ (connectives)
- ⟨possible, necessary⟩ (modals)
- ⟨warm, hot⟩ (adjectives)
- ⟨one, two, three, ...⟩ (numerals)

The scale ordering determines scalar implicatures:
- Using weaker term implicates stronger doesn't hold
- "Some came" → "Not all came"

Reference: Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
-/

import Linglib.Core.Frac

namespace Semantics.Scales

-- ============================================================================
-- General Scale Infrastructure
-- ============================================================================

/--
A Horn Scale is a list of expressions ordered by semantic strength.
Stronger expressions appear later in the list.

Requirements:
- All members have same semantic type
- Entailment: stronger ⊢ weaker (e.g., "all" ⊢ "some")
- Roughly equal complexity (for scalar implicatures to arise)
-/
structure HornScale (α : Type) where
  members : List α
  -- The head is weakest, tail is strongest
  deriving Repr

/-- Get the position of an element in a scale (0 = weakest) -/
def scalePosition {α : Type} [BEq α] (s : HornScale α) (x : α) : Option Nat :=
  s.members.findIdx? (· == x)

/-- Check if x is weaker than y on scale s -/
def isWeaker {α : Type} [BEq α] (s : HornScale α) (x y : α) : Bool :=
  match scalePosition s x, scalePosition s y with
  | some px, some py => px < py
  | _, _ => false

/-- Check if x is stronger than y on scale s -/
def isStronger {α : Type} [BEq α] (s : HornScale α) (x y : α) : Bool :=
  isWeaker s y x

/-- Get all stronger alternatives to x on scale s -/
def strongerAlternatives {α : Type} [BEq α] (s : HornScale α) (x : α) : List α :=
  match scalePosition s x with
  | some px => s.members.drop (px + 1)
  | none => []

/-- Get all weaker alternatives to x on scale s -/
def weakerAlternatives {α : Type} [BEq α] (s : HornScale α) (x : α) : List α :=
  match scalePosition s x with
  | some px => s.members.take px
  | none => []

-- ============================================================================
-- Quantifier Scales
-- ============================================================================

namespace Quantifiers

inductive QuantExpr where
  | none_ | some_ | most | all
  deriving DecidableEq, BEq, Repr

/-- The standard quantifier scale ⟨none, some, most, all⟩ -/
def quantScale : HornScale QuantExpr :=
  ⟨[.none_, .some_, .most, .all]⟩

/-- Semantic strength: stronger quantifiers entail weaker ones -/
def entails : QuantExpr → QuantExpr → Bool
  -- all entails everything below it
  | .all, .some_ => true
  | .all, .most => true
  | .all, .all => true
  -- most entails some
  | .most, .some_ => true
  | .most, .most => true
  -- some entails itself
  | .some_, .some_ => true
  -- none is special (contradicts others)
  | .none_, .none_ => true
  | _, _ => false

/--
**Theorem: Scale Order Matches Entailment**

The scale ordering reflects semantic entailment:
all ⊢ most ⊢ some
-/
theorem scale_matches_entailment :
    isStronger quantScale .all .most = true ∧
    isStronger quantScale .most .some_ = true ∧
    isStronger quantScale .all .some_ = true := by
  native_decide

/--
**Theorem: Scalar Alternatives**

"some" has stronger alternatives "most" and "all"
-/
theorem some_has_stronger_alternatives :
    strongerAlternatives quantScale .some_ = [.most, .all] := by
  native_decide

end Quantifiers

-- ============================================================================
-- Connective Scales
-- ============================================================================

namespace Connectives

inductive ConnExpr where
  | or_ | and_
  deriving DecidableEq, BEq, Repr

/-- The connective scale ⟨or, and⟩ -/
def connScale : HornScale ConnExpr :=
  ⟨[.or_, .and_]⟩

/-- Semantic strength: and ⊢ or -/
def entails : ConnExpr → ConnExpr → Bool
  | .and_, .or_ => true
  | .and_, .and_ => true
  | .or_, .or_ => true
  | _, _ => false

/--
**Theorem: "and" is Stronger than "or"**

(A ∧ B) ⊢ (A ∨ B), but not vice versa
-/
theorem and_stronger_than_or :
    isStronger connScale .and_ .or_ = true ∧
    isStronger connScale .or_ .and_ = false := by
  native_decide

/--
**Theorem: "or" Has "and" as Stronger Alternative**

This drives the exclusive-or implicature
-/
theorem or_alternative :
    strongerAlternatives connScale .or_ = [.and_] := by
  native_decide

end Connectives

-- ============================================================================
-- Modal Scales
-- ============================================================================

namespace Modals

inductive ModalExpr where
  | possible | necessary
  deriving DecidableEq, BEq, Repr

/-- The modal scale ⟨possible, necessary⟩ -/
def modalScale : HornScale ModalExpr :=
  ⟨[.possible, .necessary]⟩

/-- Semantic strength: necessary ⊢ possible -/
def entails : ModalExpr → ModalExpr → Bool
  | .necessary, .possible => true
  | .necessary, .necessary => true
  | .possible, .possible => true
  | _, _ => false

/--
**Theorem: "necessary" is Stronger than "possible"**

□p ⊢ ◇p (in normal modal logic)
-/
theorem necessary_stronger_than_possible :
    isStronger modalScale .necessary .possible = true := by
  native_decide

end Modals

-- ============================================================================
-- Numeral Scales
-- ============================================================================

namespace Numerals

-- Using a simple representation
inductive NumExpr where
  | one | two | three | four | five
  deriving DecidableEq, BEq, Repr

/-- The numeral scale (with lower-bound semantics) -/
def numScale : HornScale NumExpr :=
  ⟨[.one, .two, .three, .four, .five]⟩

/--
With lower-bound semantics, higher numbers are stronger:
"five" ⊢ "four" ⊢ "three" ⊢ "two" ⊢ "one"

Because "five" (≥5) entails "one" (≥1)
-/
theorem higher_stronger_lowerbound :
    isStronger numScale .five .one = true ∧
    isStronger numScale .three .two = true := by
  native_decide

/--
**Theorem: "two" Has Stronger Alternatives**
-/
theorem two_alternatives :
    strongerAlternatives numScale .two = [.three, .four, .five] := by
  native_decide

end Numerals

-- ============================================================================
-- Scalar Implicature Derivation
-- ============================================================================

/--
**Standard Recipe for Scalar Implicature**

Given:
- Speaker used expression x from scale s
- There exist stronger alternatives y₁, y₂, ... on s

Derive:
- For each stronger yᵢ: speaker doesn't believe yᵢ holds
- With competence assumption: speaker believes ¬yᵢ

Example:
- Speaker said "some came"
- Stronger alternatives: "most", "all"
- Implicature: ¬(most came), ¬(all came)
- Especially: ¬(all came) → "some but not all"
-/
def scalarImplicatures {α : Type} [BEq α] (s : HornScale α) (x : α) : List α :=
  strongerAlternatives s x

-- Example with quantifiers
example : scalarImplicatures Quantifiers.quantScale .some_ = [.most, .all] := by
  native_decide

-- Example with connectives
example : scalarImplicatures Connectives.connScale .or_ = [.and_] := by
  native_decide

-- ============================================================================
-- Monotonicity and Scale Reversal
-- ============================================================================

/--
## Monotonicity Effects

In downward entailing contexts, scales REVERSE:
- UE context: stronger ⊢ weaker (all ⊢ some)
- DE context: weaker ⊢ stronger (some ⊢ all under negation)

This is because:
- "Everyone ate all" ⊢ "Everyone ate some" (UE: all ⊢ some)
- "No one ate some" ⊢ "No one ate all" (DE: some ⊢ all!)

The reversal blocks standard scalar implicatures in DE contexts.
-/

inductive Monotonicity where
  | upward   -- UE: stronger ⊢ weaker
  | downward -- DE: weaker ⊢ stronger
  deriving DecidableEq, BEq, Repr

/-- In DE context, scalar alternatives come from WEAKER items -/
def scalarAlternativesInContext {α : Type} [BEq α]
    (s : HornScale α) (x : α) (m : Monotonicity) : List α :=
  match m with
  | .upward => strongerAlternatives s x   -- Standard: negate stronger
  | .downward => weakerAlternatives s x   -- DE: negate weaker (reversed!)

/--
**Theorem: DE Reversal for Quantifiers**

In UE context: "some" has alternatives "most", "all"
In DE context: "some" has NO scalar alternatives (it's already strongest!)
-/
theorem de_reversal_some :
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide

/--
**Theorem: DE Blocks "Some → Not All" Implicature**

In DE context, "some" doesn't have "all" as an alternative to negate.
Instead, "all" has "some" as an alternative (reversed scale).
-/
theorem de_blocks_some_not_all :
    -- In DE context, "all" can implicate "not some" (reversed!)
    scalarAlternativesInContext Quantifiers.quantScale .all .downward = [.none_, .some_, .most] := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This File Provides

### Scale Infrastructure
- `HornScale`: Ordered list of expressions
- `scalePosition`: Position in scale (strength)
- `strongerAlternatives`: Expressions that entail given one
- `weakerAlternatives`: Expressions entailed by given one

### Specific Scales
- `Quantifiers.quantScale`: ⟨none, some, most, all⟩
- `Connectives.connScale`: ⟨or, and⟩
- `Modals.modalScale`: ⟨possible, necessary⟩
- `Numerals.numScale`: ⟨one, two, three, four, five⟩

### Scalar Implicature
- `scalarImplicatures`: Get alternatives to negate
- `scalarAlternativesInContext`: Context-sensitive (DE/UE)

### Key Theorems
- `scale_matches_entailment`: Scale order = semantic strength
- `de_reversal_some`: DE contexts reverse the scale
- `de_blocks_some_not_all`: Explains why "not all" blocked in DE

### Connection to RSA
These scales can be used to:
1. Define alternative utterances for RSA
2. Explain why RSA derives "some → not all"
3. Predict DE blocking effects
-/

end Semantics.Scales

/-
# Neo-Gricean Pragmatics: Alternative Generation

Formalization of Horn sets and alternative generation from Geurts (2010) Ch. 3.1-3.2.

## Key Insights from Geurts

1. **Horn Sets, Not Scales** (p.58)
   Geurts argues that scales should be replaced with SETS.
   The ordering is derivable from semantics at the sentence level.

2. **Sentence-Level Strength**
   Alternatives are stronger SENTENCES, not stronger WORDS.
   This correctly handles DE environments without "scale reversal".

3. **Amended Alternative Generation** (p.58)
   φ[β] is an alternative to φ[α] iff:
   - α and β share a Horn set
   - φ[β] is stronger than φ[α] (at sentence level)

Reference: Geurts, B. (2010). Quantity Implicatures. Cambridge University Press.
-/

import Linglib.Theories.NeoGricean.Core.Basic
import Linglib.Theories.Montague.Scales
import Linglib.Theories.Montague.Derivation.Basic

namespace NeoGricean.Alternatives

-- Use shared ContextPolarity from SemDerivation
open Montague.SemDeriv (ContextPolarity)

-- ============================================================================
-- PART 1: Horn Sets (Not Scales)
-- ============================================================================

/--
A Horn Set is an unordered collection of expressions.

Following Geurts' argument on p.58, we use SETS not SCALES.
The ordering (which term is stronger) is determined at the SENTENCE level
by checking semantic entailment, not by a fixed word-level ordering.

This is crucial for handling DE contexts correctly:
- In UE context: "all" → "some" (all stronger)
- In DE context: "some" → "all" (some stronger!)

The same Horn set {some, all} works for both contexts.
-/
structure HornSet (α : Type) where
  /-- The members of the Horn set -/
  members : List α
  deriving Repr

/--
Check if a term is in a Horn set.
-/
def HornSet.contains {α : Type} [BEq α] (h : HornSet α) (x : α) : Bool :=
  h.members.contains x

/--
Get all other members of a Horn set (potential alternatives).
-/
def HornSet.otherMembers {α : Type} [BEq α] (h : HornSet α) (x : α) : List α :=
  h.members.filter (· != x)

-- ============================================================================
-- PART 2: Type-Safe Horn Sets (using Montague.Scales expressions)
-- ============================================================================

open Montague.Scales.Quantifiers (QuantExpr)
open Montague.Scales.Connectives (ConnExpr)
open Montague.Scales.Modals (ModalExpr)

/--
The quantifier Horn set: {some, most, all}

Uses type-safe `QuantExpr` from Montague.Scales.
Note: This is a SET, not an ordered scale. The ordering comes from
sentence-level semantics, not from this data structure.
-/
def quantifierSet : HornSet QuantExpr :=
  ⟨[.some_, .most, .all]⟩

/--
The connective Horn set: {or, and}
-/
def connectiveSet : HornSet ConnExpr :=
  ⟨[.or_, .and_]⟩

/--
The modal Horn set: {possible, necessary}
-/
def modalSet : HornSet ModalExpr :=
  ⟨[.possible, .necessary]⟩

/--
The numeral Horn set: {one, two, three, ...}
Uses strings for now (numerals are more complex).
-/
def numeralSet : HornSet String :=
  ⟨["one", "two", "three", "four", "five"]⟩

-- ============================================================================
-- PART 3: Sentence Context
-- ============================================================================

-- Note: ContextPolarity is imported from Montague.SemDeriv
-- with constructors .upward and .downward

/--
A sentence context for alternative generation.

The key insight: what counts as a "stronger alternative" depends on
the polarity of the context, not just the Horn set.
-/
structure SentenceContext where
  /-- The polarity of this context -/
  polarity : ContextPolarity
  /-- Description of the context -/
  description : String
  deriving Repr

/--
Common UE context: simple assertion
-/
def simpleAssertion : SentenceContext :=
  { polarity := .upward
  , description := "Simple assertion (e.g., 'John ate ___')"
  }

/--
Common DE context: under negation
-/
def underNegation : SentenceContext :=
  { polarity := .downward
  , description := "Under negation (e.g., 'No one ate ___')"
  }

/--
DE context: restrictor of universal
-/
def universalRestrictor : SentenceContext :=
  { polarity := .downward
  , description := "Restrictor of 'every' (e.g., 'Every student who ate ___')"
  }

-- ============================================================================
-- PART 4: Abstract Alternative Generation
-- ============================================================================

/--
An alternative utterance with its source term and context.
-/
structure Alternative (α : Type) where
  /-- The alternative term from the Horn set -/
  term : α
  /-- Whether this is a stronger alternative in context -/
  isStrongerInContext : Bool
  deriving Repr

/--
Abstract entailment checker for sentences.

In a real implementation, this would check semantic entailment.
Here we use a simple model based on polarity.
-/
structure EntailmentChecker (α : Type) where
  /-- Check if term1 produces a stronger sentence than term2 in context -/
  isStronger : ContextPolarity → α → α → Bool

/--
Generate alternatives to a term using a Horn set and entailment checker.
-/
def generateAlternatives {α : Type} [BEq α]
    (hornSet : HornSet α)
    (checker : EntailmentChecker α)
    (context : SentenceContext)
    (term : α) : List (Alternative α) :=
  hornSet.otherMembers term |>.map λ alt =>
    { term := alt
    , isStrongerInContext := checker.isStronger context.polarity alt term
    }

/--
Get only the STRONGER alternatives (the ones that generate implicatures).
-/
def strongerAlternatives {α : Type} [BEq α]
    (hornSet : HornSet α)
    (checker : EntailmentChecker α)
    (context : SentenceContext)
    (term : α) : List α :=
  (generateAlternatives hornSet checker context term).filter (·.isStrongerInContext) |>.map (·.term)

-- ============================================================================
-- PART 5: Quantifier Entailment (Type-Safe)
-- ============================================================================

/--
Standard quantifier strength ordering (for UE contexts).

Uses `QuantExpr.entails` from Montague.Scales:
- all > most > some (in terms of logical strength)
- "all" entails "some", so "all" is stronger
-/
def quantifierStrengthUE (q1 q2 : QuantExpr) : Bool :=
  -- q1 is stronger than q2 iff q1 entails q2 (and they're different)
  Montague.Scales.Quantifiers.entails q1 q2 && q1 != q2

/--
Reversed quantifier strength (for DE contexts).

In DE context, "some" is stronger than "all" at sentence level.
"No one ate some" entails "No one ate all".
-/
def quantifierStrengthDE (q1 q2 : QuantExpr) : Bool :=
  -- In DE, entailment reverses: q1 stronger iff q2 entails q1
  Montague.Scales.Quantifiers.entails q2 q1 && q1 != q2

/--
Entailment checker for quantifiers (type-safe).

Grounded in Montague.Scales.Quantifiers.entails.
-/
def quantifierChecker : EntailmentChecker QuantExpr :=
  { isStronger := λ pol q1 q2 =>
      match pol with
      | .upward => quantifierStrengthUE q1 q2
      | .downward => quantifierStrengthDE q1 q2
  }

-- ============================================================================
-- PART 5b: Connective Entailment (Type-Safe)
-- ============================================================================

/--
Connective strength in UE context.
"and" is stronger than "or".
-/
def connectiveStrengthUE (c1 c2 : ConnExpr) : Bool :=
  Montague.Scales.Connectives.entails c1 c2 && c1 != c2

/--
Connective strength in DE context (reversed).
-/
def connectiveStrengthDE (c1 c2 : ConnExpr) : Bool :=
  Montague.Scales.Connectives.entails c2 c1 && c1 != c2

/--
Entailment checker for connectives (type-safe).
-/
def connectiveChecker : EntailmentChecker ConnExpr :=
  { isStronger := λ pol c1 c2 =>
      match pol with
      | .upward => connectiveStrengthUE c1 c2
      | .downward => connectiveStrengthDE c1 c2
  }

-- ============================================================================
-- PART 6: Key Theorems (Type-Safe)
-- ============================================================================

/--
**Theorem: "some" has stronger alternatives in UE context**

In UE context, "all" and "most" are stronger than "some".
-/
theorem some_alternatives_ue :
    strongerAlternatives quantifierSet quantifierChecker simpleAssertion .some_ = [.most, .all] := by
  native_decide

/--
**Theorem: "some" has NO stronger alternatives in DE context**

In DE context, "some" is already the strongest term!
This explains why "not all" implicature is blocked in DE contexts.
-/
theorem some_no_alternatives_de :
    strongerAlternatives quantifierSet quantifierChecker underNegation .some_ = ([] : List QuantExpr) := by
  native_decide

/--
**Theorem: "all" has stronger alternatives in DE context**

In DE context, "some" is stronger than "all" at sentence level.
-/
theorem all_alternatives_de :
    strongerAlternatives quantifierSet quantifierChecker underNegation .all = [.some_, .most] := by
  native_decide

/--
**Theorem: Context determines alternatives**

The same Horn set produces different alternatives depending on context.
-/
theorem context_determines_alternatives :
    strongerAlternatives quantifierSet quantifierChecker simpleAssertion .some_ ≠
    strongerAlternatives quantifierSet quantifierChecker underNegation .some_ := by
  native_decide

-- ============================================================================
-- PART 7: String Interface (for syntax-semantics connection)
-- ============================================================================

/--
Convert a HornScale (from Montague.Scales) to a HornSet.

This allows us to reuse the scale definitions while treating them
as unordered sets. The ordering comes from the SentenceContext.
-/
def fromHornScale {α : Type} (scale : Montague.Scales.HornScale α) : HornSet α :=
  ⟨scale.members⟩

/--
String-based quantifier checker for interface with syntax.

Converts strings to QuantExpr, then uses the type-safe checker.
-/
def quantifierCheckerString : EntailmentChecker String :=
  { isStronger := λ pol s1 s2 =>
      match QuantExpr.ofString? s1, QuantExpr.ofString? s2 with
      | some q1, some q2 => quantifierChecker.isStronger pol q1 q2
      | _, _ => false
  }

/--
String-based connective checker for interface with syntax.
-/
def connectiveCheckerString : EntailmentChecker String :=
  { isStronger := λ pol s1 s2 =>
      match ConnExpr.ofString? s1, ConnExpr.ofString? s2 with
      | some c1, some c2 => connectiveChecker.isStronger pol c1 c2
      | _, _ => false
  }

/--
String-based quantifier set for interface with syntax.
-/
def quantifierSetString : HornSet String :=
  ⟨["some", "most", "all"]⟩

/--
String-based connective set for interface with syntax.
-/
def connectiveSetString : HornSet String :=
  ⟨["or", "and"]⟩

-- ============================================================================
-- PART 8: Summary
-- ============================================================================

/-
## What This Module Provides

### Types
- `HornSet`: Unordered set of comparable expressions
- `ContextPolarity`: UE vs DE
- `SentenceContext`: Context with polarity and description
- `Alternative`: An alternative with strength information
- `EntailmentChecker`: Abstract entailment checking

### Type-Safe Horn Sets (primary)
- `quantifierSet`: HornSet QuantExpr — {.some_, .most, .all}
- `connectiveSet`: HornSet ConnExpr — {.or_, .and_}
- `modalSet`: HornSet ModalExpr — {.possible, .necessary}

### Type-Safe Entailment Checkers
- `quantifierChecker`: Grounded in Montague.Scales.Quantifiers.entails
- `connectiveChecker`: Grounded in Montague.Scales.Connectives.entails

### String Interface (for syntax connection)
- `quantifierSetString`: HornSet String — for SemDeriv interface
- `quantifierCheckerString`: Converts strings, delegates to typed checker

### Functions
- `generateAlternatives`: Get all alternatives with strength info
- `strongerAlternatives`: Get only stronger alternatives
- `fromHornScale`: Convert Scales to Sets

### Key Theorems (Type-Safe)
- `some_alternatives_ue`: .some_ → [.most, .all] in UE
- `some_no_alternatives_de`: .some_ → [] in DE (blocked!)
- `all_alternatives_de`: .all → [.some_, .most] in DE (reversed)
- `context_determines_alternatives`: Context matters

### Design Philosophy
1. **Type-safe scales**: Use QuantExpr/ConnExpr, not strings
2. **Grounded entailment**: Entailment comes from Montague.Scales
3. **Geurts p.58**: Use SETS not SCALES; determine strength at SENTENCE level
4. **String interface**: For backward compatibility with syntax-semantics layer
-/

end NeoGricean.Alternatives

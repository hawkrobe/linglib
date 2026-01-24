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

import Linglib.Theories.NeoGricean.Basic
import Linglib.Theories.Montague.Scales

namespace NeoGricean.Alternatives

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
-- PART 2: Standard Horn Sets
-- ============================================================================

/--
The quantifier Horn set: {some, most, all}

Note: This is a SET, not an ordered scale. The ordering comes from
sentence-level semantics, not from this data structure.
-/
def quantifierSet : HornSet String :=
  ⟨["some", "most", "all"]⟩

/--
The connective Horn set: {or, and}
-/
def connectiveSet : HornSet String :=
  ⟨["or", "and"]⟩

/--
The modal Horn set: {possible, necessary}
-/
def modalSet : HornSet String :=
  ⟨["possible", "necessary"]⟩

/--
The numeral Horn set: {one, two, three, ...}
-/
def numeralSet : HornSet String :=
  ⟨["one", "two", "three", "four", "five"]⟩

-- ============================================================================
-- PART 3: Sentence Context
-- ============================================================================

/--
Context type determines which direction is "stronger".

In UE context, more specific/restrictive is stronger.
In DE context, the entailment pattern reverses.
-/
inductive ContextPolarity where
  | upwardEntailing   -- Default: stronger = more informative
  | downwardEntailing -- Reversed: weaker word = stronger sentence
  deriving DecidableEq, BEq, Repr

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
  { polarity := .upwardEntailing
  , description := "Simple assertion (e.g., 'John ate ___')"
  }

/--
Common DE context: under negation
-/
def underNegation : SentenceContext :=
  { polarity := .downwardEntailing
  , description := "Under negation (e.g., 'No one ate ___')"
  }

/--
DE context: restrictor of universal
-/
def universalRestrictor : SentenceContext :=
  { polarity := .downwardEntailing
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
  hornSet.otherMembers term |>.map fun alt =>
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
-- PART 5: Quantifier Entailment (Concrete Example)
-- ============================================================================

/--
Standard quantifier strength ordering (for UE contexts).

all > most > some (in terms of logical strength)
"all" entails "some", so "all" is stronger.
-/
def quantifierStrengthUE (q1 q2 : String) : Bool :=
  -- q1 is stronger than q2 in UE context
  match q1, q2 with
  | "all", "most" => true
  | "all", "some" => true
  | "most", "some" => true
  | _, _ => false

/--
Reversed quantifier strength (for DE contexts).

In DE context, "some" is stronger than "all" at sentence level.
"No one ate some" entails "No one ate all".
-/
def quantifierStrengthDE (q1 q2 : String) : Bool :=
  -- q1 is stronger than q2 in DE context (REVERSED)
  match q1, q2 with
  | "some", "most" => true
  | "some", "all" => true
  | "most", "all" => true
  | _, _ => false

/--
Entailment checker for quantifiers.
-/
def quantifierChecker : EntailmentChecker String :=
  { isStronger := fun pol q1 q2 =>
      match pol with
      | .upwardEntailing => quantifierStrengthUE q1 q2
      | .downwardEntailing => quantifierStrengthDE q1 q2
  }

-- ============================================================================
-- PART 6: Key Theorems
-- ============================================================================

/--
**Theorem: "some" has stronger alternatives in UE context**

In UE context, "all" and "most" are stronger than "some".
-/
theorem some_alternatives_ue :
    strongerAlternatives quantifierSet quantifierChecker simpleAssertion "some" = ["most", "all"] := by
  native_decide

/--
**Theorem: "some" has NO stronger alternatives in DE context**

In DE context, "some" is already the strongest term!
This explains why "not all" implicature is blocked in DE contexts.
-/
theorem some_no_alternatives_de :
    strongerAlternatives quantifierSet quantifierChecker underNegation "some" = ([] : List String) := by
  native_decide

/--
**Theorem: "all" has stronger alternatives in DE context**

In DE context, "some" is stronger than "all" at sentence level.
-/
theorem all_alternatives_de :
    strongerAlternatives quantifierSet quantifierChecker underNegation "all" = ["some", "most"] := by
  native_decide

/--
**Theorem: Context determines alternatives**

The same Horn set produces different alternatives depending on context.
-/
theorem context_determines_alternatives :
    strongerAlternatives quantifierSet quantifierChecker simpleAssertion "some" ≠
    strongerAlternatives quantifierSet quantifierChecker underNegation "some" := by
  native_decide

-- ============================================================================
-- PART 7: Connection to Montague.Scales
-- ============================================================================

/--
Convert a HornScale (from Montague.Scales) to a HornSet.

This allows us to reuse the scale definitions while treating them
as unordered sets. The ordering comes from the SentenceContext.
-/
def fromHornScale {α : Type} (scale : Montague.Scales.HornScale α) : HornSet α :=
  ⟨scale.members⟩

-- Import the scales and convert to sets
open Montague.Scales in
def quantifierSetFromScale : HornSet Quantifiers.QuantExpr :=
  fromHornScale Quantifiers.quantScale

open Montague.Scales in
def connectiveSetFromScale : HornSet Connectives.ConnExpr :=
  fromHornScale Connectives.connScale

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

### Horn Sets
- `quantifierSet`: {some, most, all}
- `connectiveSet`: {or, and}
- `modalSet`: {possible, necessary}
- `numeralSet`: {one, two, ...}

### Functions
- `generateAlternatives`: Get all alternatives with strength info
- `strongerAlternatives`: Get only stronger alternatives
- `fromHornScale`: Convert Scales to Sets

### Key Theorems
- `some_alternatives_ue`: "some" → [most, all] in UE
- `some_no_alternatives_de`: "some" → [] in DE (blocked!)
- `all_alternatives_de`: "all" → [some, most] in DE (reversed)
- `context_determines_alternatives`: Context matters

### Design Philosophy (Geurts p.58)
1. Use SETS not SCALES for Horn sets
2. Determine strength at SENTENCE level
3. Context polarity determines which alternatives are "stronger"
4. This correctly handles DE blocking without "scale reversal" fiction
-/

end NeoGricean.Alternatives

/-
# Neo-Gricean Pragmatics: Alternative Generation

Formalization of Horn sets and alternative generation from Geurts (2010) Ch. 3.1-3.2,
extended with M-alternatives for manner implicatures (Horn 1984, Rett 2015).

## Two Types of Pragmatic Alternatives

### Q-Alternatives (Quantity/Informativity)
From Geurts (2010):
- Differ in INFORMATIVITY (logical strength)
- Example: "some" vs "all" — different truth conditions
- Generate Q-implicatures via Quantity maxim
- Context-sensitive: strength depends on polarity (UE vs DE)

### M-Alternatives (Manner/Form Cost)
From Horn (1984), Rett (2015):
- Differ in FORM COST (markedness)
- Example: "as tall as" vs "as short as" — same truth conditions in equatives
- Generate R-implicatures via Manner maxim (Division of Pragmatic Labor)
- Construction-sensitive: only in polar-invariant constructions

## Key Insights

1. **Horn Sets, Not Scales** (Geurts p.58)
   Use SETS not ordered SCALES. Ordering comes from sentence-level semantics.

2. **Q vs M Distinction** (Horn 1984)
   Q-alternatives compete on informativity; M-alternatives compete on form cost.
   These are orthogonal dimensions of pragmatic competition.

3. **Polar Variance** (Rett 2015)
   M-alternatives only exist in polar-INVARIANT constructions where
   antonyms have the same truth conditions.

## References

- Geurts, B. (2010). Quantity Implicatures. Cambridge University Press.
- Horn, L. (1984). Toward a new taxonomy for pragmatic inference.
- Rett, J. (2015). The Semantics of Evaluativity. Oxford University Press.
-/

import Linglib.Theories.NeoGricean.Core.Basic
import Linglib.Theories.NeoGricean.Core.Markedness
import Linglib.Theories.Montague.Scales
import Linglib.Theories.Montague.Core.Derivation
import Linglib.Phenomena.Semantics.Evaluativity
import Mathlib.Data.Rat.Defs

namespace NeoGricean.Alternatives

-- Use shared ContextPolarity from Montague.Core.Polarity
open Montague.Core.Polarity (ContextPolarity)
open NeoGricean.Markedness
open Phenomena.Semantics.Evaluativity

-- ============================================================================
-- PART 0: Alternative Types (Q vs M)
-- ============================================================================

/--
Types of pragmatic alternatives.

Following Horn (1984) and Levinson (2000):
- **Q-alternatives**: Compete on informativity (Quantity principle)
- **M-alternatives**: Compete on form cost (Manner principle)

These generate different types of implicatures via different mechanisms.
-/
inductive AlternativeType where
  | quantity  -- Q-alternatives: differ in informativity
  | manner    -- M-alternatives: differ in form cost
  deriving Repr, DecidableEq, BEq

/--
A unified pragmatic alternative.

Captures both Q-alternatives and M-alternatives with their relevant properties.
-/
structure PragmaticAlternative where
  /-- Type of alternative (Q vs M) -/
  altType : AlternativeType
  /-- The alternative form -/
  form : String
  /-- The original form being compared to -/
  originalForm : String
  /-- Is this alternative "better" (stronger for Q, cheaper for M)? -/
  isBetter : Bool
  /-- Explanation of the comparison -/
  explanation : String
  deriving Repr

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
      | .nonMonotonic => false  -- No scalar alternatives in NM contexts
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
      | .nonMonotonic => false  -- No scalar alternatives in NM contexts
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
-- PART 8: M-Alternatives (Manner/Form Cost)
-- ============================================================================

/--
Polar variance: do antonyms have the same truth conditions in this construction?

This determines whether M-alternatives exist:
- Polar-VARIANT: "taller than" ≠ "shorter than" → no M-alternatives
- Polar-INVARIANT: "as tall as" = "as short as" → M-alternatives exist

From Rett (2015) Chapter 5.
-/
inductive PolarVariance where
  | variant    -- Different truth conditions (comparatives, positives)
  | invariant  -- Same truth conditions (equatives, questions)
  deriving Repr, DecidableEq, BEq

/--
Polar variance by adjectival construction type.
-/
def polarVariance : AdjectivalConstruction → PolarVariance
  | .positive => .variant
  | .comparative => .variant
  | .equative => .invariant
  | .degreeQuestion => .invariant
  | .measurePhrase => .variant

/--
An M-alternative set: forms differing in cost but not truth conditions.

Unlike Q-alternatives (which differ in informativity), M-alternatives are
EQUIVALENT in meaning but differ in production cost.
-/
structure MAlternativeSet where
  /-- The marked (costlier) form -/
  marked : String
  /-- The unmarked (cheaper) form -/
  unmarked : String
  /-- The dimension they share (e.g., "height") -/
  dimension : String
  /-- The cost difference between forms -/
  costDifference : ℚ
  /-- Construction where they're equivalent -/
  construction : AdjectivalConstruction
  deriving Repr

instance : BEq MAlternativeSet where
  beq s1 s2 := s1.marked == s2.marked && s1.unmarked == s2.unmarked &&
               s1.dimension == s2.dimension && s1.construction == s2.construction

/--
Generate M-alternatives from an antonym pair.

M-alternatives are generated when:
1. The construction is polar-invariant (antonyms semantically equivalent)
2. Markedness can be determined for the pair

Returns `none` if no M-alternatives exist.
-/
def generateMAlternatives {max : Nat}
    (adj1 adj2 : GradableAdjWithMorphology max)
    (construction : AdjectivalConstruction) : Option MAlternativeSet :=
  -- Only generate M-alternatives for polar-invariant constructions
  if polarVariance construction != .invariant then
    none
  else
    -- Compute which form is marked
    match computeMarked adj1 adj2 with
    | none => none  -- Cannot determine markedness
    | some markedForm =>
      let unmarkedForm := if markedForm == adj1.form then adj2.form else adj1.form
      some {
        marked := markedForm
        unmarked := unmarkedForm
        dimension := adj1.dimension
        costDifference := Markedness.costDifference
        construction := construction
      }

/--
Check if a form is the marked member of an M-alternative pair.
-/
def isMarkedInMAlternatives {max : Nat}
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology max)
    (construction : AdjectivalConstruction) : Bool :=
  match generateMAlternatives adj1 adj2 construction with
  | none => false
  | some mAlt => mAlt.marked == form

/--
Get the M-alternative for a form (if any).
-/
def getMAlternative {max : Nat}
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology max)
    (construction : AdjectivalConstruction) : Option String :=
  match generateMAlternatives adj1 adj2 construction with
  | none => none
  | some mAlt =>
    if mAlt.marked == form then some mAlt.unmarked
    else if mAlt.unmarked == form then some mAlt.marked
    else none

-- ============================================================================
-- PART 9: M-Alternative Theorems
-- ============================================================================

/--
M-alternatives exist in equative constructions.
-/
theorem equative_has_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .equative).isSome = true := by
  native_decide

/--
M-alternatives exist in degree question constructions.
-/
theorem question_has_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .degreeQuestion).isSome = true := by
  native_decide

/--
M-alternatives do NOT exist in comparative constructions.
-/
theorem comparative_no_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .comparative).isNone = true := by
  native_decide

/--
M-alternatives do NOT exist in positive constructions.
-/
theorem positive_no_m_alternatives :
    (generateMAlternatives tall_with_morphology short_with_morphology .positive).isNone = true := by
  native_decide

/--
"short" is the marked member in equative M-alternatives.
-/
theorem short_is_marked_in_equative :
    isMarkedInMAlternatives "short" tall_with_morphology short_with_morphology .equative = true := by
  native_decide

/--
"tall" is NOT the marked member in equative M-alternatives.
-/
theorem tall_is_not_marked_in_equative :
    isMarkedInMAlternatives "tall" tall_with_morphology short_with_morphology .equative = false := by
  native_decide

-- ============================================================================
-- PART 10: Unified Alternative Generation
-- ============================================================================

/--
Generate all pragmatic alternatives (both Q and M) for a form.

This is the unified entry point for alternative generation.
-/
def generateAllAlternatives {max : Nat}
    (form : String)
    (adj1 adj2 : GradableAdjWithMorphology max)
    (construction : AdjectivalConstruction)
    (context : SentenceContext) : List PragmaticAlternative :=
  let mAlts := match getMAlternative form adj1 adj2 construction with
    | some alt =>
      let isMarked := isMarkedInMAlternatives form adj1 adj2 construction
      [{ altType := .manner
       , form := alt
       , originalForm := form
       , isBetter := isMarked  -- If original is marked, alternative is better (cheaper)
       , explanation := if isMarked then
           s!"M-alternative: '{alt}' is cheaper than '{form}'"
         else
           s!"M-alternative: '{alt}' is costlier than '{form}'"
       }]
    | none => []
  -- Q-alternatives would be added here based on Horn sets
  -- For now, just return M-alternatives
  mAlts

-- ============================================================================
-- PART 11: Q vs M Comparison
-- ============================================================================

/--
Key distinction between Q-alternatives and M-alternatives.
-/
def alternativeComparison : String :=
"
| Property          | Q-Alternatives           | M-Alternatives              |
|-------------------|--------------------------|------------------------------|
| Compete on        | Informativity            | Form cost (markedness)       |
| Truth conditions  | Different                | Same (in construction)       |
| Maxim             | Quantity (say enough)    | Manner (be brief)            |
| Implicature       | Scalar implicature       | Manner implicature           |
| Context-sensitive | Yes (UE vs DE polarity)  | Yes (polar-invariant only)   |
| Example           | some/all                 | as tall as/as short as       |

Q-alternatives generate 'not all' from 'some' (informativity competition).
M-alternatives generate evaluativity from marked forms (cost competition).
"

-- ============================================================================
-- PART 12: Summary
-- ============================================================================

/-
## What This Module Provides

### Alternative Types
- `AlternativeType`: Q (quantity) vs M (manner)
- `PragmaticAlternative`: Unified alternative with type and properties

### Q-Alternative Infrastructure
- `HornSet`: Unordered set of comparable expressions
- `ContextPolarity`: UE vs DE
- `SentenceContext`: Context with polarity
- `Alternative`: Q-alternative with strength info
- `EntailmentChecker`: Abstract entailment checking
- `generateAlternatives`: Generate Q-alternatives
- `strongerAlternatives`: Get stronger Q-alternatives

### M-Alternative Infrastructure
- `PolarVariance`: variant vs invariant constructions
- `MAlternativeSet`: Forms differing in cost, not meaning
- `generateMAlternatives`: Generate M-alternatives for a construction
- `isMarkedInMAlternatives`: Check if form is marked
- `getMAlternative`: Get the alternative to a form

### Type-Safe Horn Sets
- `quantifierSet`: {.some_, .most, .all}
- `connectiveSet`: {.or_, .and_}
- `modalSet`: {.possible, .necessary}

### Key Theorems

**Q-Alternative Theorems:**
- `some_alternatives_ue`: some → [most, all] in UE
- `some_no_alternatives_de`: some → [] in DE (blocked!)
- `all_alternatives_de`: all → [some, most] in DE (reversed)
- `context_determines_alternatives`: Context matters

**M-Alternative Theorems:**
- `equative_has_m_alternatives`: Equatives license M-competition
- `question_has_m_alternatives`: Questions license M-competition
- `comparative_no_m_alternatives`: Comparatives don't
- `positive_no_m_alternatives`: Positives don't
- `short_is_marked_in_equative`: "short" is marked in equatives

### Design Philosophy
1. **Unified framework**: Both Q and M are pragmatic alternatives
2. **Orthogonal dimensions**: Q competes on informativity, M on cost
3. **Context-sensitive**: Both depend on context (polarity for Q, construction for M)
4. **Grounded**: Q in Montague.Scales, M in Markedness
-/

end NeoGricean.Alternatives

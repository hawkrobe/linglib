/-
# Gradable Adjective Theory Infrastructure

This module defines the `AdjectiveTheory` structure for organizing semantic
analyses of gradable adjectives (tall, happy, expensive, etc.).

## Key Issues

Gradable adjectives raise several semantic questions:

1. **Vagueness**: What counts as "tall"? Context-dependent threshold.
2. **Comparison**: "John is taller than Mary" — comparative morphology.
3. **Degree modification**: "very tall", "slightly happy" — degree operators.
4. **Antonymy**: Is "short" the contradictory or contrary of "tall"?

## Architecture

This module imports from `Fragments.Degrees` for the core types:
- `Degree`: The underlying scale (height, happiness, etc.)
- `Threshold`: Contextual cutoff for the positive form
- `NegationType`: Contradictory vs. contrary antonyms
- `ThresholdPair`: Two thresholds for contrary antonyms with gap

The theory structure wraps these in Montague's framework:
- Positive form: degree > θ
- Antonym: either contradictory (degree ≤ θ) or contrary (degree < θ_neg)

## Comparison with ModalTheory

| Aspect        | ModalTheory                        | AdjectiveTheory                    |
|---------------|------------------------------------|------------------------------------|
| Core types    | ModalForce, Proposition            | Degree, Threshold, NegationType    |
| Parameters    | Accessibility relation / backgrounds | Threshold(s), antonym type        |
| Key question  | What's the modal base?             | Where's the threshold? Contrary?   |

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification.
- Lassiter, D. & Goodman, N. (2017). Adjectival vagueness in a Bayesian model.
- Tessler, M. H. & Franke, M. (2020). Not unreasonable.
- Cruse, D. A. (1986). Lexical Semantics.
-/

import Linglib.Theories.Montague.Domain.Degree
import Linglib.Theories.Montague.Basic

namespace Montague.Adjective

open Montague.Domain.Degrees

-- Adjective Scale Types

/--
Scale type for a gradable adjective.

Following Kennedy (2007):
- **Open**: No inherent minimum or maximum (tall, expensive)
- **Lower closed**: Has a minimum, no maximum (wet, bent)
- **Upper closed**: Has a maximum, no minimum (dry, straight)
- **Closed**: Has both minimum and maximum (full, empty)

Scale type affects:
- Default threshold (minimum for lower-closed, standard for open)
- Compatibility with degree modifiers ("completely full" vs *"completely tall")
-/
inductive ScaleType where
  | open_        -- tall, expensive (no inherent bounds)
  | lowerClosed  -- wet, bent (minimum at 0)
  | upperClosed  -- dry, straight (maximum at top)
  | closed       -- full, empty (both bounds)
  deriving Repr, DecidableEq, BEq

-- Antonym Relations

/--
The relation between a positive form and its antonym.

Uses `NegationType` from `Fragments.Degrees`:
- **Contradictory**: P and ¬P partition the space (no gap)
- **Contrary**: P and Q can both be false (gap region)

Example:
- "tall" / "not tall" — contradictory (same threshold, flipped)
- "tall" / "short" — typically contrary (different thresholds, gap)
- "happy" / "unhappy" — contrary (polar opposites with gap)

This matters because "not short" ≠ "tall" when the relation is contrary.
-/
abbrev AntonymRelation := NegationType

-- Adjective Lexical Entry

/--
A gradable adjective lexical entry.

Bundles:
- Surface form ("tall", "happy")
- Scale structure (what's being measured, bounds)
- Antonym information (what's the antonym, what relation)

The actual threshold is NOT part of the lexical entry — it's contextual.
This is the key insight from Kennedy (2007): thresholds are supplied by context.
-/
structure GradableAdjEntry (max : Nat) where
  /-- Surface form -/
  form : String
  /-- Scale type (open, closed, etc.) -/
  scaleType : ScaleType
  /-- Dimension being measured (for documentation) -/
  dimension : String
  /-- Antonym form (if any) -/
  antonymForm : Option String := none
  /-- Relation to antonym (if any) -/
  antonymRelation : Option AntonymRelation := none
  deriving Repr

-- Adjective Theory

/--
A semantic theory for gradable adjectives.

Each theory specifies how to compute truth given:
- A degree value (the entity's position on the scale)
- Threshold parameter(s) (contextually determined)

## Theories

1. **Single threshold** (standard): "tall" = degree > θ
   - Antonym uses same threshold: "short" = degree < θ or degree ≤ θ

2. **Two threshold / Contrary** (Tessler & Franke):
   - Positive: degree > θ_pos
   - Antonym: degree < θ_neg where θ_neg < θ_pos
   - Gap: θ_neg ≤ degree ≤ θ_pos

The theory choice affects whether antonyms are contradictory or contrary.
-/
structure AdjectiveTheory (max : Nat) where
  /-- Name of the theory -/
  name : String
  /-- Academic citation -/
  citation : String
  /-- Does this theory support contrary antonyms (two thresholds)? -/
  supportsContrary : Bool
  /-- Positive form meaning: given degree and threshold, is positive true? -/
  positiveMeaning : Degree max → Threshold max → Bool
  /-- Contradictory antonym meaning (if not using contrary) -/
  contradictoryAntonym : Degree max → Threshold max → Bool
  /-- Contrary antonym meaning (if supported) — uses ThresholdPair -/
  contraryAntonym : Degree max → ThresholdPair max → Bool := λ _ _ => false

-- Standard Theory: Single Threshold

/--
Standard threshold semantics (Kennedy 2007, Lassiter & Goodman 2017).

- Positive: degree > θ
- Antonym (contradictory): degree ≤ θ

This is appropriate when antonyms are true contradictories:
- "tall" / "not tall" — no gap
- But potentially misleading for "tall" / "short" if they're contrary
-/
def standardTheory (max : Nat) : AdjectiveTheory max where
  name := "Standard Threshold"
  citation := "Kennedy (2007), Lassiter & Goodman (2017)"
  supportsContrary := false
  positiveMeaning := λ d θ => d.toNat > θ.toNat
  contradictoryAntonym := λ d θ => d.toNat ≤ θ.toNat

-- Contrary Theory: Two Thresholds

/--
Contrary antonym semantics (Tessler & Franke 2020).

- Positive: degree > θ_pos
- Antonym (contrary): degree < θ_neg
- Gap: θ_neg ≤ degree ≤ θ_pos

This captures polar opposite antonyms like "happy" / "unhappy".
-/
def contraryTheory (max : Nat) : AdjectiveTheory max where
  name := "Contrary Antonyms (Two Threshold)"
  citation := "Tessler & Franke (2020), Cruse (1986)"
  supportsContrary := true
  positiveMeaning := λ d θ => d.toNat > θ.toNat
  contradictoryAntonym := λ d θ => d.toNat ≤ θ.toNat
  contraryAntonym := λ d tp => d.toNat < tp.neg.toNat

-- Derived Operations

/--
Check if a degree is in the gap region (for contrary theories).

The gap is where both positive and antonym are false:
- Not positive: degree ≤ θ_pos
- Not contrary antonym: degree ≥ θ_neg
-/
def AdjectiveTheory.inGap {max : Nat} (T : AdjectiveTheory max)
    (d : Degree max) (tp : ThresholdPair max) : Bool :=
  if T.supportsContrary then
    inGapRegion d tp
  else
    false  -- No gap in contradictory theories

/--
Negated antonym meaning: "not unhappy".

If antonym is contrary: ¬(degree < θ_neg) = degree ≥ θ_neg
If antonym is contradictory: ¬(degree ≤ θ) = degree > θ (same as positive!)
-/
def AdjectiveTheory.negatedAntonym {max : Nat} (T : AdjectiveTheory max)
    (d : Degree max) (tp : ThresholdPair max) : Bool :=
  if T.supportsContrary then
    d.toNat ≥ tp.neg.toNat  -- Includes gap AND positive region
  else
    T.positiveMeaning d tp.pos  -- Collapses to positive

-- Lexical Entries

-- Concrete lexical entries (tall, short, happy, etc.) are defined in:
-- `Fragments/English/Predicates/Adjectival.lean`
--
-- This module provides only the theoretical infrastructure.

-- Theorems

/--
Standard theory has no gap (by definition, supportsContrary = false).
-/
theorem standard_no_gap : (standardTheory 4).supportsContrary = false := rfl

/--
Contrary theory supports gaps (by definition, supportsContrary = true).
-/
theorem contrary_supports_gap : (contraryTheory 4).supportsContrary = true := rfl

/--
Example: degree 2 is in the gap for θ_neg = 2, θ_pos = 3.
-/
def exampleDegree : Degree 4 := ⟨⟨2, by omega⟩⟩
def exampleThresholds : ThresholdPair 4 :=
  { pos := ⟨⟨3, by omega⟩⟩, neg := ⟨⟨2, by omega⟩⟩, gap_exists := by decide }

theorem example_in_gap : inGapRegion exampleDegree exampleThresholds = true := by native_decide

/--
In standard theory, negated antonym = positive (double negation cancels).
This is because supportsContrary = false, so negatedAntonym falls through to positiveMeaning.
-/
theorem standard_double_neg_cancels :
    (standardTheory 4).negatedAntonym exampleDegree exampleThresholds =
    (standardTheory 4).positiveMeaning exampleDegree exampleThresholds.pos := rfl

/--
In contrary theory, negated antonym ≠ positive (gap region differs).

"not unhappy" covers gap, "happy" does not.
Degree 2 with θ_neg = 2, θ_pos = 3: in gap, so "not unhappy" but not "happy"
-/
theorem contrary_double_neg_differs :
    (contraryTheory 4).negatedAntonym exampleDegree exampleThresholds = true ∧
    (contraryTheory 4).positiveMeaning exampleDegree exampleThresholds.pos = false := by
  native_decide

-- Summary

/-
## Summary: Gradable Adjective Semantics

### Key Types (from Fragments.Degrees)
- `Degree max`: Position on the scale
- `Threshold max`: Contextual cutoff
- `NegationType`: Contradictory vs. contrary
- `ThresholdPair max`: Two thresholds for contrary antonyms

### Theories
- `standardTheory`: Single threshold, contradictory antonyms
- `contraryTheory`: Two thresholds, contrary antonyms with gap

### Results
- `standard_no_gap`: No gap in standard theory
- `contrary_has_gap`: Gap exists in contrary theory
- `standard_double_neg_cancels`: "not short" = "tall" in standard
- `contrary_double_neg_differs`: "not unhappy" ≠ "happy" in contrary

### Usage
Models importing gradable adjectives should:
1. Import this module
2. Choose a theory (standard vs contrary)
3. Get grounded semantics from the theory's meaning functions
-/

end Montague.Adjective

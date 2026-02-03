/-
# Double Negation: Empirical Data

Theory-neutral data on Double Negation Elimination (DNE) and its interaction
with anaphora in dynamic semantics.

## The Phenomenon

In classical logic, ¬¬φ ↔ φ (Double Negation Elimination).

In standard dynamic semantics, this FAILS for anaphora:
- "A man walked in. He sat down." (OK)
- "It's not the case that no man walked in. He sat down." (??)

The puzzle: semantically these should be equivalent, but anaphora differs.

## Key Properties

1. **DNE for truth**: ¬¬φ and φ have the same truth conditions
2. **DNE for anaphora**: In standard DS, ¬¬φ and φ differ in dref accessibility
3. **BUS/ICDRT solution**: Bilateral/flat update validates DNE for anaphora too

## References

- Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
- Hofmann, L. (2025). Anaphoric accessibility with flat update. S&P.
-/

namespace Phenomena.Negation.DoubleNegation

-- ============================================================================
-- Part 1: Basic DNE Data
-- ============================================================================

/--
A DNE datum comparing original and double-negated versions.
-/
structure DNEDatum where
  /-- The original sentence with indefinite -/
  original : String
  /-- The double-negated version -/
  doubleNegated : String
  /-- Follow-up sentence with anaphora -/
  followUp : String
  /-- The anaphoric element -/
  anaphor : String
  /-- Is original + follow-up felicitous? -/
  originalFelicitous : Bool
  /-- Is double-negated + follow-up felicitous? -/
  doubleNegFelicitous : Bool
  /-- Should they be equivalent (by DNE)? -/
  shouldBeEquivalent : Bool
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Basic existential -/
def basicExistential : DNEDatum := {
  original := "A man walked in."
  doubleNegated := "It's not the case that no man walked in."
  followUp := "He sat down."
  anaphor := "he"
  originalFelicitous := true
  doubleNegFelicitous := true  -- In BUS/ICDRT
  shouldBeEquivalent := true
  notes := "Basic test case for DNE with anaphora"
  source := "Elliott & Sudo (2025)"
}

/-- Bathroom pattern -/
def bathroomDNE : DNEDatum := {
  original := "There's a bathroom."
  doubleNegated := "It's not the case that there's no bathroom."
  followUp := "It's upstairs."
  anaphor := "it"
  originalFelicitous := true
  doubleNegFelicitous := true
  shouldBeEquivalent := true
  notes := "Bathroom sentence DNE pattern"
  source := "Elliott & Sudo (2025)"
}

/-- More complex structure -/
def complexDNE : DNEDatum := {
  original := "A student solved every problem."
  doubleNegated := "It's not the case that no student solved every problem."
  followUp := "She was proud."
  anaphor := "she"
  originalFelicitous := true
  doubleNegFelicitous := true
  shouldBeEquivalent := true
  notes := "DNE with complex quantifier structure"
  source := "Novel example"
}

-- ============================================================================
-- Part 2: Standard DS Predictions (DNE Failure)
-- ============================================================================

/--
In standard dynamic semantics, DNE fails for anaphora.

The negative dimension "traps" discourse referents.
-/
structure StandardDSPrediction where
  sentence : String
  standardDSResult : String
  drefAccessible : Bool
  notes : String := ""
  deriving Repr

def standardDSNegation : StandardDSPrediction := {
  sentence := "No man walked in."
  standardDSResult := "Tests that no extension has a man walking in"
  drefAccessible := false
  notes := "In standard DS, negation tests without introducing drefs"
}

def standardDSDoubleNeg : StandardDSPrediction := {
  sentence := "It's not the case that no man walked in."
  standardDSResult := "Tests that it's not the case that no man walked in"
  drefAccessible := false
  notes := "Outer negation doesn't recover the inner dref"
}

-- ============================================================================
-- Part 3: BUS Predictions (DNE Success)
-- ============================================================================

/--
In bilateral semantics, negation SWAPS positive and negative.

¬¬φ = φ definitionally, so DNE holds for anaphora.
-/
structure BUSPrediction where
  sentence : String
  positiveUpdate : String
  negativeUpdate : String
  drefAccessible : Bool
  notes : String := ""
  deriving Repr

def busNegation : BUSPrediction := {
  sentence := "No man walked in."
  positiveUpdate := "[∃x.man(x) ∧ walked_in(x)]⁻"
  negativeUpdate := "[∃x.man(x) ∧ walked_in(x)]⁺"
  drefAccessible := false  -- In positive dimension
  notes := "Negation swaps: positive becomes the 'no man' reading"
}

def busDoubleNeg : BUSPrediction := {
  sentence := "It's not the case that no man walked in."
  positiveUpdate := "[∃x.man(x) ∧ walked_in(x)]⁺"
  negativeUpdate := "[∃x.man(x) ∧ walked_in(x)]⁻"
  drefAccessible := true  -- Back to original!
  notes := "Double negation: swap twice = identity"
}

-- ============================================================================
-- Part 4: ICDRT Predictions (Flat Update)
-- ============================================================================

/--
In ICDRT, drefs are introduced GLOBALLY (flat), tracked by propositional drefs.
-/
structure ICDRTPrediction where
  sentence : String
  flatUpdate : String
  propDref : String
  drefAccessible : Bool
  notes : String := ""
  deriving Repr

def icdrtNegation : ICDRTPrediction := {
  sentence := "No man walked in."
  flatUpdate := "Introduce x globally, propositional dref p tracks ∅"
  propDref := "p = ∅ (no worlds where man walked in)"
  drefAccessible := true  -- Globally introduced!
  notes := "x is introduced but p says it has no referent anywhere"
}

def icdrtDoubleNeg : ICDRTPrediction := {
  sentence := "It's not the case that no man walked in."
  flatUpdate := "Introduce x globally, propositional dref p tracks worlds"
  propDref := "p = worlds where some man walked in"
  drefAccessible := true
  notes := "x accessible in worlds where inner negation fails"
}

-- ============================================================================
-- Part 5: Empirical Judgments
-- ============================================================================

/--
Empirical judgment on DNE felicity.
-/
structure JudgmentDatum where
  discourse : List String
  felicitous : Bool
  certainty : String  -- "clear", "marginal", "controversial"
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Clear case: original -/
def clearOriginal : JudgmentDatum := {
  discourse := ["A man walked in.", "He sat down."]
  felicitous := true
  certainty := "clear"
  notes := "Uncontroversially felicitous"
  source := "Standard data"
}

/-- Clear case: single negation blocks -/
def clearNegBlocks : JudgmentDatum := {
  discourse := ["No man walked in.", "He sat down."]
  felicitous := false
  certainty := "clear"
  notes := "Uncontroversially infelicitous"
  source := "Standard data"
}

/-- Test case: double negation -/
def testDoubleNeg : JudgmentDatum := {
  discourse := ["It's not the case that no man walked in.", "He sat down."]
  felicitous := true
  certainty := "marginal"
  notes := "Judgments vary; BUS/ICDRT predict OK"
  source := "Elliott & Sudo (2025)"
}

/-- More natural double negation -/
def naturalDoubleNeg : JudgmentDatum := {
  discourse := ["It's not true that nobody came.", "They're in the garden."]
  felicitous := true
  certainty := "clear"
  notes := "More natural phrasing improves judgments"
  source := "Elliott & Sudo (2025)"
}

-- ============================================================================
-- Part 6: Triple Negation and Beyond
-- ============================================================================

/--
Triple negation: ¬¬¬φ = ¬φ
-/
def tripleNegation : DNEDatum := {
  original := "A man walked in."
  doubleNegated := "It's not the case that it's not the case that no man walked in."
  followUp := "He sat down."
  anaphor := "he"
  originalFelicitous := true
  doubleNegFelicitous := false  -- Triple = single negation
  shouldBeEquivalent := false
  notes := "Triple negation = single negation, blocks anaphora"
  source := "Logical prediction"
}

-- ============================================================================
-- Part 7: Collected Data
-- ============================================================================

/-- All DNE test cases -/
def dneData : List DNEDatum := [
  basicExistential,
  bathroomDNE,
  complexDNE,
  tripleNegation
]

/-- Standard DS predictions -/
def standardDSPredictions : List StandardDSPrediction := [
  standardDSNegation,
  standardDSDoubleNeg
]

/-- BUS predictions -/
def busPredictions : List BUSPrediction := [
  busNegation,
  busDoubleNeg
]

/-- ICDRT predictions -/
def icdrtPredictions : List ICDRTPrediction := [
  icdrtNegation,
  icdrtDoubleNeg
]

/-- Empirical judgments -/
def judgments : List JudgmentDatum := [
  clearOriginal,
  clearNegBlocks,
  testDoubleNeg,
  naturalDoubleNeg
]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `DNEDatum`: Comparison of original vs double-negated
- `StandardDSPrediction`: What standard DS predicts
- `BUSPrediction`: What BUS predicts
- `ICDRTPrediction`: What ICDRT predicts
- `JudgmentDatum`: Empirical felicity judgments

### Key Examples
- `basicExistential`: "A man walked in" vs "It's not the case that no man..."
- `bathroomDNE`: Bathroom pattern with DNE
- `testDoubleNeg`: Critical test case for theories

### Theory Comparison

| Theory | DNE for Truth | DNE for Anaphora |
|--------|--------------|------------------|
| Standard DS | Yes | No |
| BUS | Yes | Yes |
| ICDRT | Yes | Yes |

### Theoretical Significance

DNE for anaphora is a key diagnostic:
- Standard DS: ¬ is a test, loses drefs
- BUS: ¬ swaps positive and negative, DNE by swap∘swap = id
- ICDRT: Flat update, drefs always global
-/

end Phenomena.Negation.DoubleNegation

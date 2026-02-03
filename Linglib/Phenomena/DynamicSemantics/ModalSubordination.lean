/-
# Modal Subordination: Empirical Data

Theory-neutral data on modal subordination - discourse patterns where
anaphora to entities introduced under modals is licensed.

## The Phenomenon

"A wolf might come in. It would eat you first."

The pronoun "it" in the second sentence refers to the wolf introduced
under "might" in the first sentence. This is surprising because:
1. The wolf only exists in modal worlds
2. Yet "would" can access it

## Key Properties

1. **Modal context persistence**: Modals can establish contexts that persist
2. **Would/could continuation**: Certain modals continue the modal context
3. **Indicative blocks**: "A wolf might come in. It eats you." is odd
4. **Connection to counterfactuals**: Similar to counterfactual conditionals

## References

- Roberts, C. (1989). Modal Subordination and Pronominal Anaphora in Discourse.
- Stone, M. (1997). The Anaphoric Parallel between Modality and Tense.
- Hofmann, L. (2025). Anaphoric accessibility with flat update. S&P.
-/

namespace Phenomena.DynamicSemantics.ModalSubordination

-- ============================================================================
-- Part 1: Basic Modal Subordination
-- ============================================================================

/--
A modal subordination datum.
-/
structure ModalSubDatum where
  /-- First sentence (introduces entity under modal) -/
  sentence1 : String
  /-- Second sentence (with anaphora) -/
  sentence2 : String
  /-- The modal in sentence 1 -/
  modal1 : String
  /-- The modal/mood in sentence 2 -/
  modal2 : String
  /-- The anaphoric element -/
  anaphor : String
  /-- The antecedent -/
  antecedent : String
  /-- Is the discourse felicitous? -/
  felicitous : Bool
  /-- Notes -/
  notes : String := ""
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Classic wolf example -/
def wolfMightWould : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It would eat you first."
  modal1 := "might"
  modal2 := "would"
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := true
  notes := "Classic example: might...would is felicitous"
  source := "Roberts (1989)"
}

/-- With could instead of would -/
def wolfMightCould : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It could eat you first."
  modal1 := "might"
  modal2 := "could"
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := true
  notes := "Could also continues the modal context"
  source := "Roberts (1989)"
}

/-- Burglar variant -/
def burglarMightWould : ModalSubDatum := {
  sentence1 := "A burglar might break in."
  sentence2 := "He would steal the jewelry."
  modal1 := "might"
  modal2 := "would"
  anaphor := "he"
  antecedent := "a burglar"
  felicitous := true
  notes := "Same pattern with different content"
  source := "Roberts (1989)"
}

-- ============================================================================
-- Part 2: Infelicitous Contrasts
-- ============================================================================

/-- Indicative blocks -/
def wolfMightIndicative : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It eats you first."
  modal1 := "might"
  modal2 := "indicative"
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := false
  notes := "Indicative doesn't continue the modal context"
  source := "Roberts (1989)"
}

/-- Will doesn't work either -/
def wolfMightWill : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It will eat you first."
  modal1 := "might"
  modal2 := "will"
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := false
  notes := "'Will' asserts rather than subordinates"
  source := "Roberts (1989)"
}

/-- Must doesn't work -/
def wolfMightMust : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It must eat you first."
  modal1 := "might"
  modal2 := "must"
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := false
  notes := "'Must' is epistemic necessity, doesn't subordinate"
  source := "Novel example"
}

-- ============================================================================
-- Part 3: Different Introducing Modals
-- ============================================================================

/-- Could...would -/
def wolfCouldWould : ModalSubDatum := {
  sentence1 := "A wolf could come in."
  sentence2 := "It would eat you first."
  modal1 := "could"
  modal2 := "would"
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := true
  notes := "Could introduces, would continues"
  source := "Roberts (1989)"
}

/-- May...would (deontic reading) -/
def visitorMayWould : ModalSubDatum := {
  sentence1 := "A visitor may arrive."
  sentence2 := "They would need a badge."
  modal1 := "may"
  modal2 := "would"
  anaphor := "they"
  antecedent := "a visitor"
  felicitous := true
  notes := "Deontic 'may' can also introduce"
  source := "Novel example"
}

/-- Probably...would (less clear) -/
def wolfProbablyWould : ModalSubDatum := {
  sentence1 := "A wolf will probably come in."
  sentence2 := "It would eat you first."
  modal1 := "probably"
  modal2 := "would"
  anaphor := "it"
  antecedent := "a wolf"
  felicitous := false
  notes := "'Probably' doesn't establish subordination context"
  source := "Novel example"
}

-- ============================================================================
-- Part 4: Counterfactual Connection
-- ============================================================================

/--
Modal subordination connects to counterfactual conditionals.

"If a wolf came in, it would eat you." has similar structure.
-/
structure CounterfactualDatum where
  conditional : String
  antecedent : String
  consequent : String
  anaphor : String
  antecedentNP : String
  felicitous : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

/-- Counterfactual wolf -/
def counterfactualWolf : CounterfactualDatum := {
  conditional := "If a wolf came in, it would eat you first."
  antecedent := "a wolf came in"
  consequent := "it would eat you first"
  anaphor := "it"
  antecedentNP := "a wolf"
  felicitous := true
  notes := "Same binding as modal subordination"
  source := "Roberts (1989)"
}

/-- Counterfactual with indicative consequent -/
def counterfactualIndicative : CounterfactualDatum := {
  conditional := "If a wolf came in, it eats you first."
  antecedent := "a wolf came in"
  consequent := "it eats you first"
  anaphor := "it"
  antecedentNP := "a wolf"
  felicitous := false
  notes := "Indicative consequent doesn't work"
  source := "Novel example"
}

-- ============================================================================
-- Part 5: Three-way Classification (Hofmann 2025)
-- ============================================================================

/--
Hofmann (2025) distinguishes three accessibility classes:
1. Veridical: Entity asserted to exist
2. Hypothetical: Entity exists in considered possibilities
3. Counterfactual: Entity exists in non-actual possibilities

Modal subordination involves hypothetical → hypothetical transition.
-/
structure AccessibilityDatum where
  sentence : String
  accessibilityClass : String  -- "veridical", "hypothetical", "counterfactual"
  canAnaphorize : Bool
  notes : String := ""
  source : String := ""
  deriving Repr

def veridicalAccess : AccessibilityDatum := {
  sentence := "A wolf came in."
  accessibilityClass := "veridical"
  canAnaphorize := true
  notes := "Veridical: asserted to exist, freely accessible"
  source := "Hofmann (2025)"
}

def hypotheticalAccess : AccessibilityDatum := {
  sentence := "A wolf might come in."
  accessibilityClass := "hypothetical"
  canAnaphorize := true  -- By would/could
  notes := "Hypothetical: accessible by subordinating modals"
  source := "Hofmann (2025)"
}

def counterfactualAccess : AccessibilityDatum := {
  sentence := "If a wolf had come in..."
  accessibilityClass := "counterfactual"
  canAnaphorize := true  -- In counterfactual context
  notes := "Counterfactual: accessible in counterfactual continuation"
  source := "Hofmann (2025)"
}

-- ============================================================================
-- Part 6: Collected Data
-- ============================================================================

/-- All modal subordination examples -/
def modalSubData : List ModalSubDatum := [
  wolfMightWould,
  wolfMightCould,
  burglarMightWould,
  wolfMightIndicative,
  wolfMightWill,
  wolfMightMust,
  wolfCouldWould,
  visitorMayWould,
  wolfProbablyWould
]

/-- Felicitous modal subordination -/
def felicitousModalSub : List ModalSubDatum :=
  modalSubData.filter (·.felicitous)

/-- Infelicitous modal subordination -/
def infelicitousModalSub : List ModalSubDatum :=
  modalSubData.filter (!·.felicitous)

/-- Counterfactual examples -/
def counterfactualData : List CounterfactualDatum := [
  counterfactualWolf,
  counterfactualIndicative
]

/-- Accessibility class examples -/
def accessibilityData : List AccessibilityDatum := [
  veridicalAccess,
  hypotheticalAccess,
  counterfactualAccess
]

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Data Types
- `ModalSubDatum`: Two-sentence modal subordination
- `CounterfactualDatum`: Counterfactual conditionals
- `AccessibilityDatum`: Hofmann's accessibility classification

### Key Examples
- `wolfMightWould`: "A wolf might... It would..." (OK)
- `wolfMightIndicative`: "A wolf might... It eats..." (BAD)
- `counterfactualWolf`: If-conditional equivalent

### Patterns

| Modal1 | Modal2 | Felicitous |
|--------|--------|------------|
| might | would | Yes |
| might | could | Yes |
| could | would | Yes |
| might | indicative | No |
| might | will | No |
| might | must | No |

### Accessibility Classes (Hofmann 2025)

| Class | Example | Accessible By |
|-------|---------|---------------|
| Veridical | "A wolf came in" | Any continuation |
| Hypothetical | "A wolf might come in" | would/could |
| Counterfactual | "If a wolf had come in" | would have |

### Theoretical Relevance

Modal subordination tests:
- Dynamic semantics: How do modals affect accessibility?
- ICDRT: Propositional drefs track modal contexts
- DRT: Subordinate boxes for modal contexts
-/

end Phenomena.DynamicSemantics.ModalSubordination

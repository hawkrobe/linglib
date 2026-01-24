/-
# Free Choice: Empirical Data

Theory-neutral empirical patterns for free choice inferences.

## The Puzzle

"You may have coffee or tea" pragmatically implies:
"You may have coffee AND you may have tea"

Semantically: ◇(C∨T) ↔ ◇C ∨ ◇T (standard modal logic)
Pragmatically: ◇(C∨T) → ◇C ∧ ◇T (free choice!)

This is NOT a semantic entailment - it's a pragmatic inference.

## Key References

- Ross, A. (1944). Imperatives and Logic. Theoria.
- Kamp, H. (1973). Free Choice Permission. Proceedings of the Aristotelian Society.
- Zimmermann, T.E. (2000). Free Choice Disjunction and Epistemic Possibility.
- Geurts, B. (2010). Quantity Implicatures. Ch. 6.
-/

namespace Phenomena.FreeChoice

-- ============================================================================
-- PART 1: Basic Free Choice Data
-- ============================================================================

/--
Empirical pattern: Free choice permission.

"You may have coffee or tea" pragmatically implies:
"You may have coffee AND you may have tea"

This is NOT a semantic entailment:
- Semantically: ◇(C∨T) ↔ ◇C ∨ ◇T
- Pragmatically: ◇(C∨T) → ◇C ∧ ◇T
-/
structure FreeChoiceDatum where
  /-- The permission statement -/
  permission : String
  /-- The disjuncts -/
  disjunctA : String
  disjunctB : String
  /-- The inferred free choice reading -/
  inference : String
  /-- Is this a semantic entailment? -/
  isSemanticEntailment : Bool
  /-- Is this a pragmatic inference? -/
  isPragmaticInference : Bool
  deriving Repr

/--
Classic free choice example.
Source: Ross (1944), Kamp (1973)
-/
def coffeeOrTea : FreeChoiceDatum :=
  { permission := "You may have coffee or tea"
  , disjunctA := "coffee"
  , disjunctB := "tea"
  , inference := "You may have coffee AND you may have tea"
  , isSemanticEntailment := false  -- NOT semantic
  , isPragmaticInference := true   -- IS pragmatic
  }

/--
Free choice with activities.
Source: Kamp (1973)
-/
def readOrSleep : FreeChoiceDatum :=
  { permission := "You may read or sleep"
  , disjunctA := "read"
  , disjunctB := "sleep"
  , inference := "You may read AND you may sleep"
  , isSemanticEntailment := false
  , isPragmaticInference := true
  }

/--
Free choice with locations.
-/
def parkOrBeach : FreeChoiceDatum :=
  { permission := "You may go to the park or the beach"
  , disjunctA := "park"
  , disjunctB := "beach"
  , inference := "You may go to the park AND you may go to the beach"
  , isSemanticEntailment := false
  , isPragmaticInference := true
  }

/--
All basic free choice examples.
-/
def freeChoiceExamples : List FreeChoiceDatum :=
  [coffeeOrTea, readOrSleep, parkOrBeach]

-- ============================================================================
-- PART 2: Ross's Paradox
-- ============================================================================

/--
Ross's Paradox: The puzzle that motivated free choice research.

From "Post the letter" we can infer "Post the letter or burn it"
(by or-introduction). But intuitively, permission to post doesn't
give permission to burn!

Source: Ross (1944)
-/
structure RossParadoxDatum where
  /-- The original imperative/permission -/
  original : String
  /-- The derived statement (by or-intro) -/
  derived : String
  /-- Is the derivation semantically valid? -/
  semanticallyValid : Bool
  /-- Is the derivation pragmatically felicitous? -/
  pragmaticallyFelicitous : Bool
  deriving Repr

/--
Classic Ross's paradox example.
Source: Ross (1944)
-/
def postOrBurn : RossParadoxDatum :=
  { original := "Post the letter"
  , derived := "Post the letter or burn it"
  , semanticallyValid := true      -- p ⊢ p ∨ q is valid
  , pragmaticallyFelicitous := false -- But pragmatically odd!
  }

/--
Ross's paradox with permission.
-/
def mayPostOrBurn : RossParadoxDatum :=
  { original := "You may post the letter"
  , derived := "You may post the letter or burn it"
  , semanticallyValid := true
  , pragmaticallyFelicitous := false
  }

/--
All Ross's paradox examples.
-/
def rossParadoxExamples : List RossParadoxDatum :=
  [postOrBurn, mayPostOrBurn]

-- ============================================================================
-- PART 3: Free Choice with Different Modals
-- ============================================================================

/--
Free choice occurs with various modal flavors.
-/
structure ModalFreeChoiceDatum where
  /-- The modal type -/
  modalType : String
  /-- Example sentence -/
  sentence : String
  /-- Free choice inference -/
  inference : String
  /-- Does free choice arise? -/
  freeChoiceArises : Bool
  deriving Repr

/--
Deontic permission (classic case).
Source: Kamp (1973)
-/
def deonticFC : ModalFreeChoiceDatum :=
  { modalType := "deontic (permission)"
  , sentence := "You may have coffee or tea"
  , inference := "You may have coffee AND you may have tea"
  , freeChoiceArises := true
  }

/--
Epistemic possibility.
Source: Zimmermann (2000)
-/
def epistemicFC : ModalFreeChoiceDatum :=
  { modalType := "epistemic"
  , sentence := "John might be in Paris or London"
  , inference := "John might be in Paris AND John might be in London"
  , freeChoiceArises := true
  }

/--
Ability modal.
-/
def abilityFC : ModalFreeChoiceDatum :=
  { modalType := "ability"
  , sentence := "Mary can solve this problem or that one"
  , inference := "Mary can solve this one AND Mary can solve that one"
  , freeChoiceArises := true
  }

/--
All modal free choice examples.
-/
def modalFreeChoiceExamples : List ModalFreeChoiceDatum :=
  [deonticFC, epistemicFC, abilityFC]

-- ============================================================================
-- PART 4: Free Choice Cancellation
-- ============================================================================

/--
Free choice can be cancelled, showing it's pragmatic not semantic.
-/
structure FCCancellationDatum where
  /-- Original sentence with free choice -/
  original : String
  /-- Cancellation phrase -/
  cancellation : String
  /-- Combined result -/
  combined : String
  /-- Is the result felicitous? -/
  felicitous : Bool
  deriving Repr

/--
Explicit cancellation of free choice.
-/
def explicitCancellation : FCCancellationDatum :=
  { original := "You may have coffee or tea"
  , cancellation := "but I don't know which"
  , combined := "You may have coffee or tea, but I don't know which"
  , felicitous := true  -- Cancellation is possible (pragmatic!)
  }

/--
Cancellation by context.
-/
def contextualCancellation : FCCancellationDatum :=
  { original := "You may have coffee or tea"
  , cancellation := "(the menu only has one, I forget which)"
  , combined := "You may have coffee or tea (the menu only has one, I forget which)"
  , felicitous := true
  }

/--
All cancellation examples.
-/
def cancellationExamples : List FCCancellationDatum :=
  [explicitCancellation, contextualCancellation]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `FreeChoiceDatum`: Basic free choice pattern
- `RossParadoxDatum`: Ross's paradox examples
- `ModalFreeChoiceDatum`: Free choice across modal types
- `FCCancellationDatum`: Cancellation evidence

### Example Collections
- `freeChoiceExamples`: 3 basic examples
- `rossParadoxExamples`: 2 paradox examples
- `modalFreeChoiceExamples`: 3 modal types
- `cancellationExamples`: 2 cancellation examples

### Key References
- Ross (1944): Original paradox
- Kamp (1973): Free choice permission
- Zimmermann (2000): Epistemic possibility
- Geurts (2010): Modern pragmatic analysis
-/

end Phenomena.FreeChoice

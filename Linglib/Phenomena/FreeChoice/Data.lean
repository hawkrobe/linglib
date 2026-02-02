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
-- PART 5: Free Choice *Any* (Universal FCI)
-- ============================================================================

/-!
## Free Choice *Any*

Universal free choice items (FCIs) like *any* exhibit similar inference patterns
to disjunctive free choice but involve universal quantification.

"You may take any class" pragmatically implies:
- You may take Syntax (specifically)
- You may take Phonology (specifically)
- You may take Semantics (specifically)
- ... (for all classes)

This is the **exclusiveness inference**: permission applies to EACH individual
alternative, not just to "some class or other".

Key difference from disjunction:
- Disjunction: ◇(a ∨ b) → ◇a ∧ ◇b
- Universal FCI: ◇(∃x.class(x)) → ∀x.class(x) → ◇take(x)

## References

- Kadmon, N. & Landman, F. (1993). Any. Linguistics and Philosophy 16:353-422.
- Dayal, V. (1998). Any as Inherently Modal. Linguistics and Philosophy 21:433-476.
- Szabolcsi, A. (2004). Positive polarity - negative polarity. NLLT 22:409-452.
- Alsop, S. (2024). The pragmatics of free choice any.
-/

/--
Empirical pattern: Free choice *any* (universal FCI).

"You may take any class" pragmatically implies permission for each specific class.
This is the **exclusiveness inference** - distinct from simple existential permission.
-/
structure FCIAnyDatum where
  /-- The sentence with *any* -/
  sentence : String
  /-- The domain of quantification -/
  domain : String
  /-- Example domain elements -/
  domainElements : List String
  /-- The inferred reading -/
  inference : String
  /-- Does exclusiveness inference arise? -/
  exclusivenessArises : Bool
  /-- Is this inference robust to prior manipulation? -/
  robustToPriors : Bool
  deriving Repr

/--
Free choice *any* with classes.
Source: Alsop (2024)
-/
def anyClass : FCIAnyDatum :=
  { sentence := "You may take any class"
  , domain := "classes"
  , domainElements := ["Syntax", "Phonology", "Semantics"]
  , inference := "You may take Syntax AND Phonology AND Semantics (each specifically)"
  , exclusivenessArises := true
  , robustToPriors := true
  }

/--
Free choice *any* with fruits (simplified domain).
Source: Based on Kadmon & Landman (1993)
-/
def anyFruit : FCIAnyDatum :=
  { sentence := "You may take any fruit"
  , domain := "fruits"
  , domainElements := ["apple", "pear"]
  , inference := "You may take the apple AND you may take the pear (each specifically)"
  , exclusivenessArises := true
  , robustToPriors := true
  }

/--
Free choice *any* with locations.
-/
def anyRoom : FCIAnyDatum :=
  { sentence := "You may enter any room"
  , domain := "rooms"
  , domainElements := ["office", "lab", "lounge"]
  , inference := "You may enter the office AND the lab AND the lounge (each specifically)"
  , exclusivenessArises := true
  , robustToPriors := true
  }

/--
All FCI *any* examples.
-/
def fciAnyExamples : List FCIAnyDatum :=
  [anyClass, anyFruit, anyRoom]

-- ============================================================================
-- PART 6: Comparing Disjunction FC and Universal FC
-- ============================================================================

/--
Comparison between disjunctive FC and universal *any* FC.
-/
structure FCComparisonDatum where
  /-- Description of the contrast -/
  aspect : String
  /-- Disjunctive FC behavior -/
  disjunctionFC : String
  /-- Universal *any* FC behavior -/
  universalFC : String
  /-- Are they analogous? -/
  analogous : Bool
  deriving Repr

/--
Both derive free choice/exclusiveness inferences.
-/
def bothDeriveFC : FCComparisonDatum :=
  { aspect := "Core inference"
  , disjunctionFC := "◇(a ∨ b) → ◇a ∧ ◇b"
  , universalFC := "◇(∃x.P(x)) → ∀x.P(x) → ◇x"
  , analogous := true
  }

/--
Both are robust to prior manipulation.
-/
def bothRobust : FCComparisonDatum :=
  { aspect := "Robustness to priors"
  , disjunctionFC := "FCI robust, EI prior-sensitive"
  , universalFC := "Exclusiveness robust, not-every prior-sensitive"
  , analogous := true
  }

/--
Different quantificational structure.
-/
def differentStructure : FCComparisonDatum :=
  { aspect := "Quantificational structure"
  , disjunctionFC := "Disjunction of two fixed alternatives"
  , universalFC := "Universal quantification over domain"
  , analogous := false
  }

/--
All FC comparison data.
-/
def fcComparisonData : List FCComparisonDatum :=
  [bothDeriveFC, bothRobust, differentStructure]

-- ============================================================================
-- PART 7: Bathroom Disjunctions (Elliott & Sudo 2025)
-- ============================================================================

/-!
## FC with Anaphora: Bathroom Disjunctions

Elliott & Sudo (2025) identify a novel FC pattern where cross-disjunct
anaphora interacts with Free Choice:

"Either there's no bathroom or it's in a funny place"

Inference:
1. ◇(there's no bathroom)
2. ◇(there's a bathroom ∧ it's in a funny place)

The pronoun "it" in the second disjunct is bound by the existential
in the NEGATED first disjunct. This is puzzling because negation should
block binding, yet the inference requires x to be accessible.

## References

- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
-/

/--
Bathroom disjunction: FC with cross-disjunct anaphora.
-/
structure BathroomDisjunctionDatum where
  /-- The sentence -/
  sentence : String
  /-- First disjunct (typically negated existential) -/
  disjunct1 : String
  /-- Second disjunct (with anaphoric element) -/
  disjunct2 : String
  /-- The anaphoric element -/
  anaphor : String
  /-- The antecedent (under negation) -/
  antecedent : String
  /-- First FC inference -/
  inference1 : String
  /-- Second FC inference (with anaphora resolved) -/
  inference2 : String
  /-- Does cross-disjunct anaphora occur? -/
  hasCrossDisjunctAnaphora : Bool
  /-- Source -/
  source : String := "Elliott & Sudo (2025)"
  deriving Repr

/--
Classic bathroom disjunction.
Source: Elliott & Sudo (2025)
-/
def bathroomClassic : BathroomDisjunctionDatum :=
  { sentence := "Either there's no bathroom or it's in a funny place"
  , disjunct1 := "there's no bathroom"
  , disjunct2 := "it's in a funny place"
  , anaphor := "it"
  , antecedent := "there's a bathroom"
  , inference1 := "It's possible there's no bathroom"
  , inference2 := "It's possible there's a bathroom and it's in a funny place"
  , hasCrossDisjunctAnaphora := true
  }

/--
Bathroom variant with "the bathroom".
-/
def bathroomDefinite : BathroomDisjunctionDatum :=
  { sentence := "Either there's no bathroom or the bathroom is upstairs"
  , disjunct1 := "there's no bathroom"
  , disjunct2 := "the bathroom is upstairs"
  , anaphor := "the bathroom"
  , antecedent := "there's a bathroom"
  , inference1 := "It's possible there's no bathroom"
  , inference2 := "It's possible there's a bathroom and it's upstairs"
  , hasCrossDisjunctAnaphora := true
  }

/--
Similar pattern with different content.
-/
def keyExample : BathroomDisjunctionDatum :=
  { sentence := "Either I lost my key or it's in my other bag"
  , disjunct1 := "I lost my key"
  , disjunct2 := "it's in my other bag"
  , anaphor := "it"
  , antecedent := "my key exists and I have it"
  , inference1 := "It's possible I lost my key"
  , inference2 := "It's possible my key is in my other bag"
  , hasCrossDisjunctAnaphora := true
  }

/--
Negated universal variant.
-/
def nobodyExample : BathroomDisjunctionDatum :=
  { sentence := "Either nobody came or they left early"
  , disjunct1 := "nobody came"
  , disjunct2 := "they left early"
  , anaphor := "they"
  , antecedent := "somebody came"
  , inference1 := "It's possible nobody came"
  , inference2 := "It's possible somebody came and they left early"
  , hasCrossDisjunctAnaphora := true
  }

/--
All bathroom disjunction examples.
-/
def bathroomDisjunctionExamples : List BathroomDisjunctionDatum :=
  [bathroomClassic, bathroomDefinite, keyExample, nobodyExample]

-- ============================================================================
-- PART 8: FC Without Anaphora (Contrast Cases)
-- ============================================================================

/--
Standard FC without cross-disjunct anaphora (for comparison).
-/
structure StandardFCDatum where
  /-- The sentence -/
  sentence : String
  /-- The disjuncts -/
  disjuncts : List String
  /-- FC inferences -/
  inferences : List String
  /-- Any anaphora? -/
  hasAnaphora : Bool
  deriving Repr

/--
Standard FC: no anaphora.
-/
def coffeeTeaStandard : StandardFCDatum :=
  { sentence := "You may have coffee or tea"
  , disjuncts := ["have coffee", "have tea"]
  , inferences := ["You may have coffee", "You may have tea"]
  , hasAnaphora := false
  }

/--
Standard FC with independent disjuncts.
-/
def parisLondonStandard : StandardFCDatum :=
  { sentence := "John might be in Paris or London"
  , disjuncts := ["John is in Paris", "John is in London"]
  , inferences := ["John might be in Paris", "John might be in London"]
  , hasAnaphora := false
  }

/--
All standard FC examples (contrast with bathroom).
-/
def standardFCExamples : List StandardFCDatum :=
  [coffeeTeaStandard, parisLondonStandard]

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
- `FCIAnyDatum`: Universal free choice items
- `BathroomDisjunctionDatum`: FC with cross-disjunct anaphora

### Example Collections
- `freeChoiceExamples`: 3 basic examples
- `rossParadoxExamples`: 2 paradox examples
- `modalFreeChoiceExamples`: 3 modal types
- `cancellationExamples`: 2 cancellation examples
- `fciAnyExamples`: 3 universal FCI examples
- `bathroomDisjunctionExamples`: 4 bathroom-type examples

### Key References
- Ross (1944): Original paradox
- Kamp (1973): Free choice permission
- Zimmermann (2000): Epistemic possibility
- Geurts (2010): Modern pragmatic analysis
- Kadmon & Landman (1993): Free choice *any*
- Elliott & Sudo (2025): FC with anaphora
-/

end Phenomena.FreeChoice

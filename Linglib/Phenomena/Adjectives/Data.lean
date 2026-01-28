/-
# Adjective Semantics Phenomena

Empirical data testing the adjective hierarchy (Kamp 1975, Partee 1995, 2001).

## The Phenomena

Adjectives differ in their entailment patterns. A semantic theory must predict:

1. **Intersective** ("gray", "French"): "gray cat" = gray ∩ cat
2. **Subsective non-intersective** ("skillful", "good"): entails noun, but NOT intersection
3. **Non-subsective/Modal** ("alleged", "potential"): no entailment either way
4. **"Privative"** ("fake", "counterfeit"): traditionally ∩ noun = ∅, but Partee argues coercion

## Key Test Cases

- The "skillful surgeon" test: Francis is a skillful surgeon + violinist ≠ skillful violinist
- The "Is that gun real or fake?" test: noun includes both denotations (Partee 2001)
- The "alleged murderer" test: neither entails nor anti-entails "murderer"

## Data Sources

- Kamp (1975) "Two theories about adjectives"
- Parsons (1970) "Some problems concerning the logic of grammatical modifiers"
- Kamp & Partee (1995) "Prototype theory and compositionality"
- Partee (2001) "Privative Adjectives: Subsective plus Coercion"
-/

import Linglib.Phenomena.EmpiricalData

namespace Phenomena.Adjectives

open Phenomena

-- ============================================================================
-- Data Structures
-- ============================================================================

/--
An adjective entailment judgment: does the premise entail the conclusion?
-/
structure AdjectiveEntailment where
  /-- The premise sentence -/
  premise : String
  /-- The conclusion sentence -/
  conclusion : String
  /-- Does the premise entail the conclusion? -/
  entails : Bool
  /-- The adjective class being tested -/
  adjClass : String
  /-- What pattern this tests -/
  pattern : String
  deriving Repr

/--
A conjunction inference test: is the inference valid?
-/
structure ConjunctionInference where
  /-- First premise -/
  premise1 : String
  /-- Second premise (optional for single-premise cases) -/
  premise2 : Option String
  /-- The conclusion -/
  conclusion : String
  /-- Is the inference valid? -/
  valid : Bool
  /-- What pattern this tests -/
  pattern : String
  deriving Repr

/--
A felicity judgment: is the question/sentence felicitous?
-/
structure FelicityJudgment where
  /-- The sentence -/
  sentence : String
  /-- Is it felicitous? -/
  felicitous : Bool
  /-- What this demonstrates -/
  significance : String
  deriving Repr

-- ============================================================================
-- INTERSECTIVE ADJECTIVES ("gray", "French", "carnivorous")
-- ============================================================================

/-
Key property: ⟦A N⟧ = ⟦A⟧ ∩ ⟦N⟧

Test: "Julius is a gray cat" ↔ "Julius is gray" ∧ "Julius is a cat"
-/

/-- "gray cat" entails "gray" -/
def grayCat_entails_gray : AdjectiveEntailment :=
  { premise := "Julius is a gray cat"
  , conclusion := "Julius is gray"
  , entails := true
  , adjClass := "intersective"
  , pattern := "A N → A (downward entailment)"
  }

/-- "gray cat" entails "cat" -/
def grayCat_entails_cat : AdjectiveEntailment :=
  { premise := "Julius is a gray cat"
  , conclusion := "Julius is a cat"
  , entails := true
  , adjClass := "intersective"
  , pattern := "A N → N (downward entailment)"
  }

/-- "gray" + "cat" entails "gray cat" (conjunction introduction) -/
def gray_and_cat_entails_grayCat : ConjunctionInference :=
  { premise1 := "Julius is gray"
  , premise2 := some "Julius is a cat"
  , conclusion := "Julius is a gray cat"
  , valid := true
  , pattern := "A ∧ N → A N (intersective adjective)"
  }

/-- "French" is intersective: French woman = French ∩ woman -/
def frenchWoman_entails_french : AdjectiveEntailment :=
  { premise := "Marie is a French woman"
  , conclusion := "Marie is French"
  , entails := true
  , adjClass := "intersective"
  , pattern := "A N → A (nationality adjective)"
  }

/-- "carnivorous" is intersective -/
def carnivorousMammal_entails_carnivorous : AdjectiveEntailment :=
  { premise := "Fido is a carnivorous mammal"
  , conclusion := "Fido is carnivorous"
  , entails := true
  , adjClass := "intersective"
  , pattern := "A N → A (natural kind adjective)"
  }

/-- Intersective adjectives are context-independent -/
def intersective_context_independence : ConjunctionInference :=
  { premise1 := "Julius is a gray cat"
  , premise2 := some "Julius is a gray mouse"
  , conclusion := "Gray cats and gray mice are both gray"
  , valid := true
  , pattern := "same 'gray' extension in both contexts"
  }

-- ============================================================================
-- SUBSECTIVE NON-INTERSECTIVE ADJECTIVES ("skillful", "good", "typical")
-- ============================================================================

/-
Key property: ⟦A N⟧ ⊆ ⟦N⟧, but ⟦A N⟧ ≠ ⟦A⟧ ∩ ⟦N⟧

The adjective extension is RELATIVE to the noun.
-/

/-- "skillful surgeon" entails "surgeon" (subsectivity) -/
def skillfulSurgeon_entails_surgeon : AdjectiveEntailment :=
  { premise := "Francis is a skillful surgeon"
  , conclusion := "Francis is a surgeon"
  , entails := true
  , adjClass := "subsective non-intersective"
  , pattern := "A N → N (subsectivity holds)"
  }

/-- THE KEY TEST: "skillful surgeon" + "violinist" does NOT entail "skillful violinist" -/
def skillful_nonintersective : ConjunctionInference :=
  { premise1 := "Francis is a skillful surgeon"
  , premise2 := some "Francis is a violinist"
  , conclusion := "Francis is a skillful violinist"
  , valid := false  -- THIS IS THE KEY: inference is INVALID
  , pattern := "A N₁ ∧ N₂ ⊬ A N₂ (non-intersectivity)"
  }

/-- "good" is subsective but not intersective -/
def goodChef_entails_chef : AdjectiveEntailment :=
  { premise := "Alex is a good chef"
  , conclusion := "Alex is a chef"
  , entails := true
  , adjClass := "subsective non-intersective"
  , pattern := "A N → N (subsectivity)"
  }

/-- "good" is context-dependent -/
def good_nonintersective : ConjunctionInference :=
  { premise1 := "Alex is a good chef"
  , premise2 := some "Alex is a parent"
  , conclusion := "Alex is a good parent"
  , valid := false  -- Being a good chef doesn't make you a good parent
  , pattern := "A N₁ ∧ N₂ ⊬ A N₂ (context-dependence)"
  }

/-- "typical" is subsective but not intersective -/
def typicalDog_entails_dog : AdjectiveEntailment :=
  { premise := "Fido is a typical dog"
  , conclusion := "Fido is a dog"
  , entails := true
  , adjClass := "subsective non-intersective"
  , pattern := "A N → N (subsectivity)"
  }

/-- "typical" is context-dependent -/
def typical_nonintersective : ConjunctionInference :=
  { premise1 := "Fido is a typical dog"
  , premise2 := some "Fido is a pet"
  , conclusion := "Fido is a typical pet"
  , valid := false  -- A typical dog may not be a typical pet
  , pattern := "A N₁ ∧ N₂ ⊬ A N₂ (typicality is relative)"
  }

-- ============================================================================
-- NON-SUBSECTIVE / MODAL ADJECTIVES ("alleged", "potential", "putative")
-- ============================================================================

/-
Key property: NO entailment either way.

An alleged murderer may or may not be a murderer.
-/

/-- "alleged murderer" does NOT entail "murderer" -/
def allegedMurderer_not_entails_murderer : AdjectiveEntailment :=
  { premise := "John is an alleged murderer"
  , conclusion := "John is a murderer"
  , entails := false
  , adjClass := "non-subsective/modal"
  , pattern := "A N ⊬ N (no positive entailment)"
  }

/-- "alleged murderer" does NOT entail "not a murderer" -/
def allegedMurderer_not_entails_notMurderer : AdjectiveEntailment :=
  { premise := "John is an alleged murderer"
  , conclusion := "John is not a murderer"
  , entails := false
  , adjClass := "non-subsective/modal"
  , pattern := "A N ⊬ ¬N (no negative entailment)"
  }

/-- "potential" is non-subsective -/
def potentialWinner_not_entails_winner : AdjectiveEntailment :=
  { premise := "Sarah is a potential winner"
  , conclusion := "Sarah is a winner"
  , entails := false
  , adjClass := "non-subsective/modal"
  , pattern := "A N ⊬ N (potential doesn't entail actual)"
  }

/-- "putative" is non-subsective -/
def putativeFather_not_entails_father : AdjectiveEntailment :=
  { premise := "Bill is Mary's putative father"
  , conclusion := "Bill is Mary's father"
  , entails := false
  , adjClass := "non-subsective/modal"
  , pattern := "A N ⊬ N (putative doesn't entail actual)"
  }

-- ============================================================================
-- "PRIVATIVE" ADJECTIVES ("fake", "counterfeit", "fictitious")
-- ============================================================================

/-
Traditional view: ⟦A N⟧ ∩ ⟦N⟧ = ∅
"A fake gun is not a gun."

Partee (2001): Actually subsective + noun coercion!
"fake gun" = subsective within coerced "gun*" (= guns ∪ fake-guns)

Evidence: "Is that gun real or fake?" - the noun must include both!
-/

/-- Traditional view: "fake gun" entails "not a gun" -/
def fakeGun_traditionalPrivative : AdjectiveEntailment :=
  { premise := "This is a fake gun"
  , conclusion := "This is not a gun"
  , entails := true  -- Under traditional privative analysis
  , adjClass := "privative (traditional)"
  , pattern := "A N → ¬N (traditional privative)"
  }

/-- Partee's evidence: "Is that gun real or fake?" is felicitous -/
def realOrFake_felicitous : FelicityJudgment :=
  { sentence := "Is that gun real or fake?"
  , felicitous := true
  , significance := "The noun 'gun' must include both real and fake guns (Partee 2001)"
  }

/-- Partee's evidence: this would be infelicitous if "gun" excluded fake guns -/
def realOrFake_requires_coercion : FelicityJudgment :=
  { sentence := "Is that gun real or fake?"
  , felicitous := true
  , significance := "Noun coercion: 'gun' is interpreted as gun* = real-guns ∪ fake-guns"
  }

/-- "counterfeit money" patterns like "fake gun" -/
def counterfeitMoney_privateOrCoercion : AdjectiveEntailment :=
  { premise := "This is counterfeit money"
  , conclusion := "This is money"
  , entails := false  -- Depends on analysis: privative vs coercion
  , adjClass := "privative or subsective+coercion"
  , pattern := "Truth depends on whether noun is coerced"
  }

/-- "fictitious character" -/
def fictitiousCharacter : AdjectiveEntailment :=
  { premise := "Sherlock Holmes is a fictitious character"
  , conclusion := "Sherlock Holmes is a character"
  , entails := true  -- Subsective within literary domain
  , adjClass := "privative or subsective+coercion"
  , pattern := "Subsective within coerced domain of characters"
  }

-- ============================================================================
-- Collected Test Cases
-- ============================================================================

/-- All intersective adjective entailments -/
def intersectiveEntailments : List AdjectiveEntailment :=
  [ grayCat_entails_gray
  , grayCat_entails_cat
  , frenchWoman_entails_french
  , carnivorousMammal_entails_carnivorous
  ]

/-- All subsective non-intersective entailments -/
def subsectiveEntailments : List AdjectiveEntailment :=
  [ skillfulSurgeon_entails_surgeon
  , goodChef_entails_chef
  , typicalDog_entails_dog
  ]

/-- All non-subsective/modal entailments -/
def nonSubsectiveEntailments : List AdjectiveEntailment :=
  [ allegedMurderer_not_entails_murderer
  , allegedMurderer_not_entails_notMurderer
  , potentialWinner_not_entails_winner
  , putativeFather_not_entails_father
  ]

/-- The key non-intersectivity tests -/
def nonIntersectivityTests : List ConjunctionInference :=
  [ skillful_nonintersective  -- THE classic test
  , good_nonintersective
  , typical_nonintersective
  ]

/-- Intersectivity tests (should be valid) -/
def intersectivityTests : List ConjunctionInference :=
  [ gray_and_cat_entails_grayCat
  , intersective_context_independence
  ]

/-- Privative / coercion judgments -/
def privativeJudgments : List FelicityJudgment :=
  [ realOrFake_felicitous
  , realOrFake_requires_coercion
  ]

-- ============================================================================
-- Theorems About the Data
-- ============================================================================

/-- Intersective adjectives have bidirectional entailment -/
theorem intersective_bidirectional :
    grayCat_entails_gray.entails = true ∧
    grayCat_entails_cat.entails = true ∧
    gray_and_cat_entails_grayCat.valid = true := by
  native_decide

/-- Subsective adjectives have one-directional entailment -/
theorem subsective_one_direction :
    skillfulSurgeon_entails_surgeon.entails = true ∧
    skillful_nonintersective.valid = false := by
  native_decide

/-- Non-subsective adjectives have no entailment either way -/
theorem nonsubsective_no_entailment :
    allegedMurderer_not_entails_murderer.entails = false ∧
    allegedMurderer_not_entails_notMurderer.entails = false := by
  native_decide

/-- The skillful surgeon test distinguishes intersective from subsective -/
theorem skillful_surgeon_test :
    -- subsective holds
    skillfulSurgeon_entails_surgeon.entails = true ∧
    -- but intersectivity fails
    skillful_nonintersective.valid = false := by
  native_decide

/-- The "real or fake" question is felicitous (Partee's evidence) -/
theorem partee_coercion_evidence :
    realOrFake_felicitous.felicitous = true := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `AdjectiveEntailment`: premise → conclusion entailment test
- `ConjunctionInference`: premise₁ ∧ premise₂ → conclusion validity test
- `FelicityJudgment`: sentence felicity test

### Intersective Adjectives ("gray", "French")
- `grayCat_entails_gray/cat`: A N → A, A N → N
- `gray_and_cat_entails_grayCat`: A ∧ N → A N

### Subsective Non-Intersective ("skillful", "good", "typical")
- `skillfulSurgeon_entails_surgeon`: A N → N (subsective)
- `skillful_nonintersective`: A N₁ ∧ N₂ ⊬ A N₂ (THE KEY TEST)

### Non-Subsective/Modal ("alleged", "potential")
- `allegedMurderer_not_entails_murderer`: A N ⊬ N
- `allegedMurderer_not_entails_notMurderer`: A N ⊬ ¬N

### "Privative" / Coercion ("fake", "counterfeit")
- `realOrFake_felicitous`: Partee's coercion evidence

### Key Theorems
- `intersective_bidirectional`: intersectives have ↔
- `subsective_one_direction`: subsectives have → but not ←
- `nonsubsective_no_entailment`: modals have neither
- `skillful_surgeon_test`: THE diagnostic for intersectivity

## Theory Predictions (from Montague/Modification.lean)

A theory correctly predicts intersective adjectives if:
1. `intersective_equivalence` holds (PM gives ↔)
2. `pm_entails_left/right` hold (downward entailments)
3. `pm_intro` holds (conjunction introduction)

A theory should NOT apply PM to non-intersective adjectives, or it will
incorrectly validate `skillful_nonintersective`.
-/

end Phenomena.Adjectives

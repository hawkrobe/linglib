/-
# Non-Maximality: Empirical Data

Theory-neutral empirical patterns for non-maximal readings of plural sentences.

## Phenomena Covered

1. **Issue-sensitivity**: Same sentence, different contexts → different readings
2. **SWITCHES scenarios**: Maximal vs non-maximal contexts
3. **BANK ROBBERY scenario**: Fine-grained non-maximality
4. **Homogeneity removers block non-maximality**: "all" prevents weakening

## Key Insight

Non-maximal readings arise when the distinction between "all" and "some but not all"
is irrelevant for the conversational goals. The perceived truth conditions are
"weakened" to match the salient issue.

## Key References

- Krifka (1996): "Pragmatic strengthening in plural predications"
- Lasersohn (1999): "Pragmatic halos"
- Malamud (2012): Decision problems and non-maximality
- Križ (2015, 2016): Issue-based semantics
- Križ & Spector (2021): Supervaluationist approach
-/

namespace Phenomena.Plurals.NonMaximality

-- ============================================================================
-- PART 1: Issue-Sensitivity Structure
-- ============================================================================

/--
A context that makes a particular issue salient.
-/
structure ContextualIssue where
  /-- Description of the context -/
  contextDescription : String
  /-- The implicit question/issue -/
  implicitQuestion : String
  /-- Is the distinction all/some relevant? -/
  allSomeDistinctionRelevant : Bool
  deriving Repr

/--
Non-maximality datum: same sentence, different construals in different contexts.
-/
structure NonMaximalityDatum where
  /-- The sentence -/
  sentence : String
  /-- Context favoring maximal reading -/
  maximalContext : ContextualIssue
  /-- Context favoring non-maximal reading -/
  nonMaximalContext : ContextualIssue
  /-- Scenario description (same for both) -/
  scenario : String
  /-- Is sentence acceptable in maximal context? -/
  acceptableInMaximalContext : Bool
  /-- Is sentence acceptable in non-maximal context? -/
  acceptableInNonMaximalContext : Bool
  deriving Repr

-- ============================================================================
-- PART 2: SWITCHES Scenarios (Canonical Example)
-- ============================================================================

/--
The SWITCHES scenario from Križ (2015, 2016).

Context: 10 light switches, potential electrical fire hazard.
Scenario: 2 switches are on.

Key manipulation: What triggers the fire risk?
- MAXIMAL: Fire only if ALL 10 switches are on
- NON-MAXIMAL: Fire if ANY switch is on

Source: Križ (2015, 2016), dissertation (11)
-/
def switchesNonMaximality : NonMaximalityDatum :=
  { sentence := "Oh no, the switches are on!"
  , maximalContext :=
      { contextDescription := "Fire risk only if all 10 switches are on"
      , implicitQuestion := "Are all the switches on?"
      , allSomeDistinctionRelevant := true
      }
  , nonMaximalContext :=
      { contextDescription := "Fire risk if any switch is on"
      , implicitQuestion := "Are any of the switches on?"
      , allSomeDistinctionRelevant := false
      }
  , scenario := "2 of the 10 switches are on"
  , acceptableInMaximalContext := false  -- misleading
  , acceptableInNonMaximalContext := true -- acceptable
  }

/--
"All" blocks non-maximality even in permissive contexts.

Source: dissertation (17)
-/
structure AllBlocksNonMaxDatum where
  /-- Sentence without "all" -/
  plainSentence : String
  /-- Sentence with "all" -/
  allSentence : String
  /-- Context description -/
  context : String
  /-- Scenario -/
  scenario : String
  /-- Plain acceptable? -/
  plainAcceptable : Bool
  /-- All-sentence acceptable? -/
  allAcceptable : Bool
  deriving Repr

def switchesAllBlocks : AllBlocksNonMaxDatum :=
  { plainSentence := "Oh no, the switches are on!"
  , allSentence := "Oh no, all the switches are on!"
  , context := "Fire risk if any switch is on (non-maximal context)"
  , scenario := "2 of 10 switches are on"
  , plainAcceptable := true
  , allAcceptable := false  -- "all" forces maximal reading
  }

-- ============================================================================
-- PART 3: BANK ROBBERY Scenario (Fine-Grained Non-Maximality)
-- ============================================================================

/--
The BANK ROBBERY scenario from Krifka (1996).

Shows that non-maximal readings can be very fine-grained,
not just "existential" weakening.

Context: Bank vault with 4 doors in a configuration.
Some doors are parallel paths, others are sequential.

Source: Krifka (1996), dissertation (16), Figure 2.1
-/
structure BankRobberyDatum where
  /-- The sentence -/
  sentence : String
  /-- Door configuration description -/
  doorConfiguration : String
  /-- Which doors are open -/
  openDoors : List Nat
  /-- Which doors are closed -/
  closedDoors : List Nat
  /-- Is a path to the safe available? -/
  pathAvailable : Bool
  /-- Is the sentence acceptable? -/
  acceptable : Bool
  deriving Repr

/--
Configuration A: Doors 1,2 parallel, doors 3,4 parallel, must pass one from each pair.

Path exists if: (door 1 OR door 2) AND (door 3 OR door 4) open.
-/
def bankRobberyConfigA_AllOpen : BankRobberyDatum :=
  { sentence := "The doors were open."
  , doorConfiguration := "Doors 1,2 parallel (first barrier), 3,4 parallel (second barrier)"
  , openDoors := [1, 2, 3, 4]
  , closedDoors := []
  , pathAvailable := true
  , acceptable := true
  }

def bankRobberyConfigA_Door4Closed : BankRobberyDatum :=
  { sentence := "The doors were open."
  , doorConfiguration := "Doors 1,2 parallel (first barrier), 3,4 parallel (second barrier)"
  , openDoors := [1, 2, 3]
  , closedDoors := [4]
  , pathAvailable := true  -- can still reach safe via door 3
  , acceptable := true     -- non-maximal reading appropriate
  }

def bankRobberyConfigA_Door2Closed : BankRobberyDatum :=
  { sentence := "The doors were open."
  , doorConfiguration := "Doors 1,2 parallel (first barrier), 3,4 parallel (second barrier)"
  , openDoors := [1, 3, 4]
  , closedDoors := [2]
  , pathAvailable := true  -- can still reach safe via door 1
  , acceptable := true
  }

/--
Configuration B: All 4 doors in sequence (must pass all).

Path exists only if ALL doors open.
-/
def bankRobberyConfigB_AllOpen : BankRobberyDatum :=
  { sentence := "The doors were open."
  , doorConfiguration := "Doors 1,2,3,4 all in sequence"
  , openDoors := [1, 2, 3, 4]
  , closedDoors := []
  , pathAvailable := true
  , acceptable := true
  }

def bankRobberyConfigB_Door4Closed : BankRobberyDatum :=
  { sentence := "The doors were open."
  , doorConfiguration := "Doors 1,2,3,4 all in sequence"
  , openDoors := [1, 2, 3]
  , closedDoors := [4]
  , pathAvailable := false  -- blocked by door 4
  , acceptable := false     -- maximal reading required by context
  }

-- ============================================================================
-- PART 4: Problem Sets Example (Structured Non-Maximality)
-- ============================================================================

/--
The problem sets example (Križ 2015, attributed to Spector).

Shows that non-maximal readings cannot convey arbitrary information.

Context: Course with two paths to pass:
  1. Do ALL problem sets, OR
  2. Do HALF problem sets AND write essay

"He did the problem sets" should NOT be able to mean
"He did what was necessary (via either path)".

Source: Križ (2015:85), dissertation (75)
-/
structure StructuredNonMaxDatum where
  /-- The sentence -/
  sentence : String
  /-- Context description -/
  context : String
  /-- What is the issue? -/
  issue : String
  /-- Does the non-maximal reading fit the issue? -/
  nonMaxFitsIssue : Bool
  /-- Is the non-maximal reading available? -/
  nonMaxAvailable : Bool
  /-- Why or why not? -/
  explanation : String
  deriving Repr

def problemSetsExample : StructuredNonMaxDatum :=
  { sentence := "He did the problem sets."
  , context := "Course requirement: do all problem sets OR do half and write essay. John did half the problem sets and wrote an essay."
  , issue := "Did John do enough coursework to pass?"
  , nonMaxFitsIssue := true  -- "did half or all" would fit
  , nonMaxAvailable := false -- but this reading isn't available
  , explanation := "Non-maximal readings must be 'structured' - they can weaken plural predication but cannot add disjunctive conditions unrelated to the predicate."
  }

-- ============================================================================
-- PART 5: P-Truth vs Semantic Truth
-- ============================================================================

/--
Distinction between semantic truth and pragmatic truth (p-truth).

- Semantic truth: literal, compositional meaning
- P-truth: "true enough" given the contextual issue

Source: Križ (2015, 2016)
-/
structure TruthDistinctionDatum where
  /-- The sentence -/
  sentence : String
  /-- Context -/
  context : String
  /-- Scenario -/
  scenario : String
  /-- Semantically true? -/
  semanticallyTrue : Bool
  /-- P-true in context? -/
  pTrue : Bool
  /-- Issue -/
  issue : String
  deriving Repr

def switchesTruthDistinction_Maximal : TruthDistinctionDatum :=
  { sentence := "The switches are on."
  , context := "Fire risk only if all 10 on"
  , scenario := "2 of 10 switches are on"
  , semanticallyTrue := false  -- gap scenario
  , pTrue := false             -- issue distinguishes this from all-on
  , issue := "Are all the switches on?"
  }

def switchesTruthDistinction_NonMax : TruthDistinctionDatum :=
  { sentence := "The switches are on."
  , context := "Fire risk if any switch on"
  , scenario := "2 of 10 switches are on"
  , semanticallyTrue := false  -- gap scenario (same)
  , pTrue := true              -- issue groups this with all-on worlds
  , issue := "Are any of the switches on?"
  }

-- ============================================================================
-- PART 6: Strong Relevance
-- ============================================================================

/--
Strong relevance: a proposition "perfectly fits" an issue.

A proposition p is strongly relevant to issue I iff p is expressible
as a disjunction of a proper subset of I's partition cells.

Source: Križ & Spector (2021)
-/
structure StrongRelevanceDatum where
  /-- The proposition (informal) -/
  proposition : String
  /-- The issue (informal) -/
  issue : String
  /-- Is proposition strongly relevant? -/
  stronglyRelevant : Bool
  /-- Why or why not? -/
  explanation : String
  deriving Repr

def stronglyRelevantExample : StrongRelevanceDatum :=
  { proposition := "All switches are on"
  , issue := "Are all switches on?"
  , stronglyRelevant := true
  , explanation := "Proposition corresponds exactly to one partition cell"
  }

def notStronglyRelevantExample : StrongRelevanceDatum :=
  { proposition := "Switch 1 is on"
  , issue := "Are all switches on?"
  , stronglyRelevant := false
  , explanation := "Proposition makes distinctions orthogonal to the issue (switch 1 on but not all vs switch 1 on and all)"
  }

def existentialStronglyRelevant : StrongRelevanceDatum :=
  { proposition := "Some switch is on"
  , issue := "Are any switches on?"
  , stronglyRelevant := true
  , explanation := "Existential proposition corresponds to one cell of the bipartition"
  }

-- ============================================================================
-- PART 7: Developmental Stability
-- ============================================================================

/--
Non-maximality patterns are stable across development.

Children show adult-like sensitivity to context for non-maximal readings.

Source: Tieu et al. (2019), mentioned in dissertation
-/
structure DevelopmentalDatum where
  /-- Age group -/
  ageGroup : String
  /-- Construction -/
  construction : String
  /-- Finding -/
  finding : String
  deriving Repr

def tieuEtAlFinding : DevelopmentalDatum :=
  { ageGroup := "French-speaking children"
  , construction := "Plural definites"
  , finding := "Children often interpret existentially; adult-like homogeneous reading found but NOT non-homogeneous 'all' reading"
  }

-- ============================================================================
-- PART 8: Key Generalizations
-- ============================================================================

/--
Core empirical generalizations about non-maximality.
-/
structure NonMaximalityGeneralizations where
  /-- Non-max readings are issue-sensitive -/
  issueSensitive : Bool
  /-- Non-max readings require some/all distinction to be irrelevant -/
  requiresIrrelevantDistinction : Bool
  /-- "All" blocks non-maximality -/
  allBlocksNonMax : Bool
  /-- Non-max readings are "structured" (can't add arbitrary content) -/
  structured : Bool
  /-- Fine-grained non-max readings possible (not just existential) -/
  fineGrainedPossible : Bool
  /-- Conjunctions resist non-max despite having gaps -/
  conjunctionsResist : Bool
  deriving Repr

def mainGeneralizations : NonMaximalityGeneralizations :=
  { issueSensitive := true
  , requiresIrrelevantDistinction := true
  , allBlocksNonMax := true
  , structured := true
  , fineGrainedPossible := true
  , conjunctionsResist := true
  }

-- ============================================================================
-- Collections
-- ============================================================================

def canonicalExamples : List NonMaximalityDatum :=
  [switchesNonMaximality]

def bankRobberyExamples : List BankRobberyDatum :=
  [ bankRobberyConfigA_AllOpen
  , bankRobberyConfigA_Door4Closed
  , bankRobberyConfigA_Door2Closed
  , bankRobberyConfigB_AllOpen
  , bankRobberyConfigB_Door4Closed
  ]

def truthDistinctionExamples : List TruthDistinctionDatum :=
  [switchesTruthDistinction_Maximal, switchesTruthDistinction_NonMax]

def strongRelevanceExamples : List StrongRelevanceDatum :=
  [stronglyRelevantExample, notStronglyRelevantExample, existentialStronglyRelevant]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Data Types
- `ContextualIssue`: Description of salient issue in context
- `NonMaximalityDatum`: Same sentence, different contexts
- `AllBlocksNonMaxDatum`: How "all" prevents weakening
- `BankRobberyDatum`: Fine-grained non-maximality patterns
- `StructuredNonMaxDatum`: Limits on non-maximal readings
- `TruthDistinctionDatum`: Semantic vs p-truth
- `StrongRelevanceDatum`: Partition alignment

### Example Collections
- `canonicalExamples`: SWITCHES scenario
- `bankRobberyExamples`: Krifka's door configurations
- `truthDistinctionExamples`: p-truth vs semantic truth
- `strongRelevanceExamples`: Issue alignment patterns

### Key References
- Krifka (1996), Lasersohn (1999), Malamud (2012)
- Križ (2015, 2016), Križ & Spector (2021)
-/

end Phenomena.Plurals.NonMaximality

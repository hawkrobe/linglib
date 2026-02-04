/-
# Worked Examples of SDS Derivations

This module provides concrete worked examples from Erk & Herbelot (2024)
"How to Marry a Star: Probabilistic Constraints for Meaning in Context"
demonstrating how SDS constraint systems compute disambiguations.

## Key Examples from the Paper

1. **"A bat was sleeping"** - Selectional preference dominates
2. **"A player was holding a bat"** - Scenario constraint dominates
3. **"The astronomer married the star"** - Conflict → pun/zeugma
4. **"The sailor liked the port"** - Multiple ambiguous words
5. **"The coach told the star to play"** - Chained disambiguation

## Compositional Constraint Interaction

The key insight: constraints from MULTIPLE sources combine via Product of Experts:
- Selectional preferences from predicates
- Scenario constraints from context words
- World knowledge priors

The relative strengths determine interpretation.
-/

import Linglib.Theories.SDS.Core
import Linglib.Theories.SDS.ThresholdInstances

namespace SDS.Examples

open SDS.Core

-- Shared Types for Disambiguation Examples

/-- Concepts for "bat" -/
inductive BatConcept where
  | animal     -- Flying mammal
  | equipment  -- Baseball bat
  deriving Repr, BEq, DecidableEq

/-- Concepts for "star" -/
inductive StarConcept where
  | celebrity  -- Famous person
  | celestial  -- Celestial body
  deriving Repr, BEq, DecidableEq

/-- Concepts for "port" -/
inductive PortConcept where
  | harbor     -- Place where ships dock
  | wine       -- Fortified wine
  | computer   -- Computer port/connection
  deriving Repr, BEq, DecidableEq

/-- A disambiguation scenario with selectional and scenario constraints -/
structure DisambiguationScenario (C : Type) where
  /-- Name of the ambiguous word -/
  word : String
  /-- Context sentence -/
  context : String
  /-- Selectional constraint (from predicate) -/
  selectional : C → ℚ
  /-- Scenario constraint (from frame/context words) -/
  scenario : C → ℚ
  /-- Support (list of concepts) -/
  concepts : List C

instance {C : Type} : SDSConstraintSystem (DisambiguationScenario C) C where
  paramSupport s := s.concepts
  selectionalFactor s c := s.selectional c
  scenarioFactor s c := s.scenario c

-- Example 1: "A bat was sleeping" (Erk & Herbelot 2024)

/-!
## Example 1: "A bat was sleeping"

**Context**: The verb SLEEP provides a strong selectional preference.

**Constraints**:
- Selectional (SLEEP wants animate subject):
  - P(ANIMAL | subject-of-SLEEP) = 0.95
  - P(EQUIPMENT | subject-of-SLEEP) = 0.05
- Scenario (neutral, no frame activated):
  - P(ANIMAL | neutral) = 0.5
  - P(EQUIPMENT | neutral) = 0.5

**Prediction**: ANIMAL wins because selectional preference is strong.
-/

def batSleeping : DisambiguationScenario BatConcept where
  word := "bat"
  context := "A bat was sleeping"
  selectional := fun
    | .animal => 95/100     -- SLEEP strongly prefers animate
    | .equipment => 5/100   -- Equipment can't really sleep
  scenario := fun
    | .animal => 50/100     -- Neutral context
    | .equipment => 50/100
  concepts := [.animal, .equipment]

/-!
### Worked Computation

**Step 1**: Unnormalized posteriors
- unnorm(ANIMAL) = 0.95 × 0.50 = 0.475
- unnorm(EQUIPMENT) = 0.05 × 0.50 = 0.025

**Step 2**: Partition function
- Z = 0.475 + 0.025 = 0.50

**Step 3**: Normalized posteriors
- P(ANIMAL) = 0.475 / 0.50 = 0.95
- P(EQUIPMENT) = 0.025 / 0.50 = 0.05

**Result**: Strong preference for ANIMAL (95%)
-/

def batSleepingPosterior : BatConcept → ℚ :=
  SDSConstraintSystem.normalizedPosterior batSleeping

-- Verify ANIMAL wins decisively
example : batSleepingPosterior .animal > batSleepingPosterior .equipment := by native_decide

-- No conflict: selectional clearly dominates
example : hasConflict batSleeping = false := by native_decide

-- Example 2: "A player was holding a bat" (Erk & Herbelot 2024)

/-!
## Example 2: "A player was holding a bat"

**Context**: The word "player" activates a SPORTS scenario.
The verb HOLD has weak selectional preference (both concepts are holdable).

**Constraints**:
- Selectional (HOLD wants concrete object):
  - P(ANIMAL | object-of-HOLD) = 0.4 (can hold an animal)
  - P(EQUIPMENT | object-of-HOLD) = 0.6 (slightly prefer inanimate)
- Scenario (SPORTS frame from "player"):
  - P(ANIMAL | SPORTS) = 0.1
  - P(EQUIPMENT | SPORTS) = 0.9

**Prediction**: EQUIPMENT wins because scenario constraint is strong
and selectional is weak.
-/

def playerHoldingBat : DisambiguationScenario BatConcept where
  word := "bat"
  context := "A player was holding a bat"
  selectional := fun
    | .animal => 40/100     -- Can hold an animal
    | .equipment => 60/100  -- Slightly prefer inanimate objects
  scenario := fun
    | .animal => 10/100     -- SPORTS frame disfavors animals
    | .equipment => 90/100  -- SPORTS frame strongly favors equipment
  concepts := [.animal, .equipment]

/-!
### Worked Computation

**Step 1**: Unnormalized posteriors
- unnorm(ANIMAL) = 0.40 × 0.10 = 0.04
- unnorm(EQUIPMENT) = 0.60 × 0.90 = 0.54

**Step 2**: Partition function
- Z = 0.04 + 0.54 = 0.58

**Step 3**: Normalized posteriors
- P(ANIMAL) = 0.04 / 0.58 ≈ 0.069
- P(EQUIPMENT) = 0.54 / 0.58 ≈ 0.931

**Result**: Strong preference for EQUIPMENT (93%)

**Key insight**: Even though HOLD doesn't strongly select for equipment,
the SPORTS scenario from "player" tips the balance decisively.
-/

def playerBatPosterior : BatConcept → ℚ :=
  SDSConstraintSystem.normalizedPosterior playerHoldingBat

-- Verify EQUIPMENT wins
example : playerBatPosterior .equipment > playerBatPosterior .animal := by native_decide

-- No conflict: both selectional and scenario prefer equipment
-- (Even though selectional is weak, it still has equipment as argmax)
example : hasConflict playerHoldingBat = false := by native_decide

-- Example 3: "The astronomer married the star" (Erk & Herbelot 2024)

/-!
## Example 3: "The astronomer married the star"

**Context**: Competing constraints create a pun/zeugma reading.

**Constraints**:
- Selectional (MARRY wants human object):
  - P(CELEBRITY | object-of-MARRY) = 0.9
  - P(CELESTIAL | object-of-MARRY) = 0.1
- Scenario (ASTRONOMY frame from "astronomer"):
  - P(CELEBRITY | ASTRONOMY) = 0.1
  - P(CELESTIAL | ASTRONOMY) = 0.9

**Prediction**: TIE → pun/zeugma reading emerges.

This is the signature example from the paper showing how
conflicting constraints predict pragmatic ambiguity.
-/

def astronomerMarriedStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The astronomer married the star"
  selectional := fun
    | .celebrity => 90/100  -- MARRY wants human
    | .celestial => 10/100  -- Can't literally marry a star
  scenario := fun
    | .celebrity => 10/100  -- ASTRONOMY frame disfavors celebrities
    | .celestial => 90/100  -- ASTRONOMY frame strongly favors celestial
  concepts := [.celebrity, .celestial]

/-!
### Worked Computation

**Step 1**: Unnormalized posteriors
- unnorm(CELEBRITY) = 0.90 × 0.10 = 0.09
- unnorm(CELESTIAL) = 0.10 × 0.90 = 0.09

**Step 2**: Partition function
- Z = 0.09 + 0.09 = 0.18

**Step 3**: Normalized posteriors
- P(CELEBRITY) = 0.09 / 0.18 = 0.50
- P(CELESTIAL) = 0.09 / 0.18 = 0.50

**Result**: Perfect tie (50-50)

**Key insight**: When selectional and scenario constraints have equal
strength but opposite preferences, we get a tie. This predicts:
1. Pun reading (both meanings simultaneously)
2. Zeugma effect (semantic clash)
3. Garden path potential
-/

def astronomerStarPosterior : StarConcept → ℚ :=
  SDSConstraintSystem.normalizedPosterior astronomerMarriedStar

-- Verify it's a tie
example : astronomerStarPosterior .celebrity = astronomerStarPosterior .celestial := by native_decide

-- Conflict detected
example : hasConflict astronomerMarriedStar = true := by native_decide

-- Example 4: "The sailor liked the port" - Multiple Ambiguous Words

/-!
## Example 4: "The sailor liked the port"

**Context**: Both "sailor" (activates NAUTICAL scenario) and "port"
(ambiguous between harbor/wine/computer) need disambiguation.

This shows how scenario constraints propagate: "sailor" activates
NAUTICAL which then disambiguates "port".

**Constraints for "port"**:
- Selectional (LIKE is neutral):
  - P(HARBOR | object-of-LIKE) = 0.33
  - P(WINE | object-of-LIKE) = 0.33
  - P(COMPUTER | object-of-LIKE) = 0.33
- Scenario (NAUTICAL frame from "sailor"):
  - P(HARBOR | NAUTICAL) = 0.7
  - P(WINE | NAUTICAL) = 0.25 (sailors drink!)
  - P(COMPUTER | NAUTICAL) = 0.05

**Prediction**: HARBOR wins, WINE is plausible, COMPUTER unlikely.
-/

def sailorLikedPort : DisambiguationScenario PortConcept where
  word := "port"
  context := "The sailor liked the port"
  selectional := fun  -- LIKE is neutral
    | .harbor => 33/100
    | .wine => 33/100
    | .computer => 34/100
  scenario := fun  -- NAUTICAL frame from "sailor"
    | .harbor => 70/100    -- Primary nautical meaning
    | .wine => 25/100      -- Sailors historically drink port wine
    | .computer => 5/100   -- Unlikely in nautical context
  concepts := [.harbor, .wine, .computer]

/-!
### Worked Computation

**Step 1**: Unnormalized posteriors
- unnorm(HARBOR) = 0.33 × 0.70 = 0.231
- unnorm(WINE) = 0.33 × 0.25 = 0.0825
- unnorm(COMPUTER) = 0.34 × 0.05 = 0.017

**Step 2**: Partition function
- Z = 0.231 + 0.0825 + 0.017 = 0.3305

**Step 3**: Normalized posteriors
- P(HARBOR) = 0.231 / 0.3305 ≈ 0.699
- P(WINE) = 0.0825 / 0.3305 ≈ 0.250
- P(COMPUTER) = 0.017 / 0.3305 ≈ 0.051

**Result**: HARBOR (70%), WINE (25%), COMPUTER (5%)

**Key insight**: With a neutral predicate (LIKE), the scenario
constraint from "sailor" does all the disambiguation work.
WINE remains plausible due to cultural association.
-/

def sailorPortPosterior : PortConcept → ℚ :=
  SDSConstraintSystem.normalizedPosterior sailorLikedPort

-- Verify HARBOR wins
example : sailorPortPosterior .harbor > sailorPortPosterior .wine := by native_decide
example : sailorPortPosterior .wine > sailorPortPosterior .computer := by native_decide

-- Example 5: "The coach told the star to play" - Chained Disambiguation

/-!
## Example 5: "The coach told the star to play"

**Context**: Multiple words contribute to the scenario:
- "coach" → SPORTS frame
- "play" → reinforces SPORTS (or ENTERTAINMENT)

This shows how constraints from multiple words combine.

**Constraints for "star"**:
- Selectional (TELL wants animate recipient):
  - P(CELEBRITY | recipient-of-TELL) = 0.95
  - P(CELESTIAL | recipient-of-TELL) = 0.05
- Scenario (SPORTS frame from "coach" + "play"):
  - P(CELEBRITY | SPORTS) = 0.8 (sports stars are celebrities)
  - P(CELESTIAL | SPORTS) = 0.2

**Prediction**: CELEBRITY wins strongly (both constraints agree).
-/

def coachToldStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The coach told the star to play"
  selectional := fun  -- TELL wants animate
    | .celebrity => 95/100
    | .celestial => 5/100
  scenario := fun  -- SPORTS frame from "coach" + "play"
    | .celebrity => 80/100  -- Sports stars
    | .celestial => 20/100
  concepts := [.celebrity, .celestial]

/-!
### Worked Computation

**Step 1**: Unnormalized posteriors
- unnorm(CELEBRITY) = 0.95 × 0.80 = 0.76
- unnorm(CELESTIAL) = 0.05 × 0.20 = 0.01

**Step 2**: Partition function
- Z = 0.76 + 0.01 = 0.77

**Step 3**: Normalized posteriors
- P(CELEBRITY) = 0.76 / 0.77 ≈ 0.987
- P(CELESTIAL) = 0.01 / 0.77 ≈ 0.013

**Result**: CELEBRITY wins decisively (98.7%)

**Key insight**: When selectional and scenario constraints AGREE,
they reinforce each other multiplicatively, leading to very
confident disambiguation.
-/

def coachStarPosterior : StarConcept → ℚ :=
  SDSConstraintSystem.normalizedPosterior coachToldStar

-- Verify CELEBRITY wins decisively
example : coachStarPosterior .celebrity > coachStarPosterior .celestial := by native_decide

-- No conflict: both constraints prefer CELEBRITY
example : hasConflict coachToldStar = false := by native_decide

-- Example 6: Constraint Strength Interaction

/-!
## Example 6: Varying Constraint Strengths

This example shows how the RATIO of constraint strengths matters.

Consider "The child saw the bat":
- CHILD activates weak DOMESTIC scenario (pets, toys)
- SAW is perceptually neutral
- How does varying the scenario strength affect disambiguation?
-/

/-- Parameterized bat disambiguation varying scenario strength -/
def childSawBat (scenarioStrength : ℚ) : DisambiguationScenario BatConcept where
  word := "bat"
  context := "The child saw the bat"
  selectional := fun  -- SAW is neutral
    | .animal => 50/100
    | .equipment => 50/100
  scenario := fun  -- DOMESTIC scenario (varies)
    | .animal => scenarioStrength        -- Pets more likely at home
    | .equipment => 1 - scenarioStrength -- Toys/sports equipment
  concepts := [.animal, .equipment]

/-!
### Varying Scenario Strength

| Scenario Strength | P(ANIMAL) | P(EQUIPMENT) | Interpretation |
|-------------------|-----------|--------------|----------------|
| 0.5 (neutral)     | 0.50      | 0.50         | Ambiguous      |
| 0.6               | 0.60      | 0.40         | Slight animal  |
| 0.7               | 0.70      | 0.30         | Prefer animal  |
| 0.8               | 0.80      | 0.20         | Strong animal  |

With neutral selectional constraint (0.5/0.5), the scenario
constraint directly determines the posterior.
-/

-- At neutral scenario, it's ambiguous
example : SDSConstraintSystem.normalizedPosterior (childSawBat (50/100)) .animal =
          SDSConstraintSystem.normalizedPosterior (childSawBat (50/100)) .equipment := by
  native_decide

-- At strong scenario (0.7), animal wins
example : SDSConstraintSystem.normalizedPosterior (childSawBat (70/100)) .animal >
          SDSConstraintSystem.normalizedPosterior (childSawBat (70/100)) .equipment := by
  native_decide

-- Example 7: The Full "How to Marry a Star" Analysis

/-!
## Example 7: Complete Analysis of "marry a star"

The paper analyzes different contexts for "marry a star":

1. **Neutral context**: "Someone married a star"
   - Selectional dominates → CELEBRITY

2. **Astronomy context**: "The astronomer married the star"
   - Conflict → TIE

3. **Hollywood context**: "The producer married the star"
   - Both agree → CELEBRITY (reinforced)

4. **Sci-fi context**: "The alien married the star"
   - Weak conflict → depends on genre conventions
-/

/-- Neutral context: "Someone married a star" -/
def neutralMarryStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "Someone married a star"
  selectional := fun
    | .celebrity => 90/100
    | .celestial => 10/100
  scenario := fun  -- Neutral
    | .celebrity => 50/100
    | .celestial => 50/100
  concepts := [.celebrity, .celestial]

/-- Hollywood context: "The producer married the star" -/
def producerMarryStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The producer married the star"
  selectional := fun
    | .celebrity => 90/100
    | .celestial => 10/100
  scenario := fun  -- ENTERTAINMENT frame
    | .celebrity => 95/100  -- Hollywood stars
    | .celestial => 5/100
  concepts := [.celebrity, .celestial]

/-- Sci-fi context: "The alien married the star" -/
def alienMarryStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The alien married the star"
  selectional := fun  -- SCI-FI loosens constraints
    | .celebrity => 60/100  -- Aliens could marry humans
    | .celestial => 40/100  -- Or merge with celestial bodies!
  scenario := fun  -- SCIFI frame
    | .celebrity => 30/100
    | .celestial => 70/100  -- Space context
  concepts := [.celebrity, .celestial]

/-!
### Comparison of Contexts

| Context | Sel(C) | Sel(S) | Scen(C) | Scen(S) | P(CELEBRITY) |
|---------|--------|--------|---------|---------|--------------|
| Neutral | 0.90   | 0.10   | 0.50    | 0.50    | 0.90         |
| Astronomer | 0.90 | 0.10  | 0.10    | 0.90    | 0.50 (TIE)   |
| Producer | 0.90  | 0.10   | 0.95    | 0.05    | 0.99         |
| Alien   | 0.60   | 0.40   | 0.30    | 0.70    | 0.39         |

The "alien" case is interesting: even though CELESTIAL wins,
it's not a clear pun because the selectional constraint is
also weakened in sci-fi contexts.
-/

-- Neutral: CELEBRITY wins (selectional dominates)
example : SDSConstraintSystem.normalizedPosterior neutralMarryStar .celebrity >
          SDSConstraintSystem.normalizedPosterior neutralMarryStar .celestial := by
  native_decide

-- Astronomer: TIE
example : SDSConstraintSystem.normalizedPosterior astronomerMarriedStar .celebrity =
          SDSConstraintSystem.normalizedPosterior astronomerMarriedStar .celestial := by
  native_decide

-- Producer: CELEBRITY wins decisively (reinforcement)
example : SDSConstraintSystem.normalizedPosterior producerMarryStar .celebrity >
          SDSConstraintSystem.normalizedPosterior producerMarryStar .celestial := by
  native_decide

-- Alien: CELESTIAL wins (scenario dominates weakened selectional)
example : SDSConstraintSystem.normalizedPosterior alienMarryStar .celestial >
          SDSConstraintSystem.normalizedPosterior alienMarryStar .celebrity := by
  native_decide

-- Conflict detection
-- Note: hasConflict checks if argmax differs. With neutral scenario (0.5/0.5),
-- the first element wins ties, so argmax = celebrity = selectional argmax → no conflict
example : hasConflict neutralMarryStar = false := by native_decide   -- Both argmax = celebrity
example : hasConflict astronomerMarriedStar = true := by native_decide  -- Equal conflict
example : hasConflict producerMarryStar = false := by native_decide   -- Both agree
example : hasConflict alienMarryStar = true := by native_decide       -- Weak conflict

-- Summary

/-!
## Summary: Compositional Constraint Interaction

### Key Principles from Erk & Herbelot (2024)

1. **Product of Experts**: Constraints multiply, they don't add
   - Both must be satisfied for high probability
   - One zero kills the interpretation

2. **Relative Strength Matters**: The RATIO determines the winner
   - Strong selectional + weak scenario → selectional wins
   - Weak selectional + strong scenario → scenario wins
   - Equal strengths → conflict/tie

3. **Scenario Propagation**: Context words activate frames
   - "sailor" → NAUTICAL
   - "coach" + "play" → SPORTS
   - "astronomer" → ASTRONOMY

4. **Conflict Predicts Pragmatic Effects**:
   - Tie → pun/zeugma reading
   - Near-tie → garden path potential
   - Agreement → confident interpretation

### Computational Pattern

For word w in context C with concepts {c₁, c₂, ...}:

```
P(cᵢ | C) ∝ P_sel(cᵢ | predicate) × P_scen(cᵢ | frame(C))
```

Where:
- P_sel comes from selectional preferences of governing predicates
- P_scen comes from scenario/frame activated by context words
- The product is normalized over all concepts
-/

end SDS.Examples

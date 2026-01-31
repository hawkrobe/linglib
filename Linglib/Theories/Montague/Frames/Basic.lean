/-
# Semantic Frames and Scenarios

Frame-based constraints for meaning in context.

## Overview

Frames (Fillmore 1982) and scenarios/scripts (Schank & Abelson 1977)
provide background knowledge that constrains interpretation:

- RESTAURANT scenario: waiter, menu, bill, tip
- SPORTS scenario: player, game, equipment, score
- ASTRONOMY scenario: telescope, star, planet, observation

## Connection to SDS

Erk & Herbelot (2024) model scenarios as distributions over concepts:
```
P(concept | scenario) = topic-word distribution (LDA-style)
```

Combined with selectional preferences via Product of Experts:
```
P(concept | context) ∝ P_selectional(concept) × P_scenario(concept)
```

## Connection to RSA

Scenarios can be modeled in RSA as:
1. World priors that encode scenario-typical configurations
2. QUDs that partition by scenario-relevant distinctions
3. A latent "Goal" variable (as in RSAScenario.Goal)

## References

- Fillmore, C.J. (1982). Frame Semantics. In Linguistics in the Morning Calm.
- Schank, R.C. & Abelson, R.P. (1977). Scripts, Plans, Goals and Understanding.
- Erk, K. & Herbelot, A. (2024). How to Marry a Star. Journal of Semantics.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.ProductOfExperts

namespace Montague.Frames

-- ============================================================================
-- PART 1: Basic Frame Structure
-- ============================================================================

/-!
## Frames as Distributions over Concepts

A frame/scenario is a coherent situation type that makes certain
concepts more or less likely.
-/

/--
A scenario is a named distribution over concepts.

This models the "scenario constraint" in SDS:
P(concept | scenario)
-/
structure Scenario (Concept : Type) where
  /-- Name of the scenario (e.g., "SPORTS", "ASTRONOMY") -/
  name : String
  /-- Distribution: P(concept | scenario) -/
  conceptDist : Concept → ℚ

/--
A scenario mixture: distribution over scenarios.

When the scenario itself is uncertain, we have a mixture:
P(concept) = Σ_s P(s) × P(concept | s)
-/
structure ScenarioMix (Scenario : Type) where
  /-- Distribution over scenarios: P(scenario) -/
  dist : Scenario → ℚ

-- ============================================================================
-- PART 2: Frame Elements
-- ============================================================================

/-!
## Frame Elements

A frame defines a set of roles (frame elements) and their typical fillers.

COMMERCIAL_TRANSACTION frame:
- Buyer: human
- Seller: human or organization
- Goods: artifact or service
- Money: currency
- etc.
-/

/--
A frame element (role within a frame).
-/
structure FrameElement (Concept : Type) where
  /-- Name of the element (e.g., "Buyer", "Goods") -/
  name : String
  /-- Typical fillers: P(concept | this element) -/
  typicalFillers : Concept → ℚ

/--
A full frame definition with its elements.
-/
structure FrameDef (Concept : Type) where
  /-- Frame name -/
  name : String
  /-- Frame elements with their filler distributions -/
  elements : List (FrameElement Concept)
  /-- Overall scenario distribution (for concepts not tied to specific elements) -/
  scenarioBase : Concept → ℚ

-- ============================================================================
-- PART 3: Example Scenarios
-- ============================================================================

/-!
## Example Scenarios for the "bat" and "star" examples
-/

/-- Concept type for bat disambiguation -/
inductive BatConcept where
  | animal      -- flying mammal
  | equipment   -- baseball bat
  deriving Repr, BEq, DecidableEq

/-- Concept type for star disambiguation -/
inductive StarConcept where
  | celestial   -- astronomical object
  | celebrity   -- famous person
  deriving Repr, BEq, DecidableEq

/-- WILDLIFE scenario: nature, animals, habitat -/
def wildlifeScenario : Scenario BatConcept :=
  { name := "WILDLIFE"
  , conceptDist := fun
      | .animal => 95/100
      | .equipment => 5/100
  }

/-- SPORTS scenario: games, players, equipment -/
def sportsScenario : Scenario BatConcept :=
  { name := "SPORTS"
  , conceptDist := fun
      | .animal => 5/100
      | .equipment => 95/100
  }

/-- ASTRONOMY scenario: telescopes, observations, celestial objects -/
def astronomyScenario : Scenario StarConcept :=
  { name := "ASTRONOMY"
  , conceptDist := fun
      | .celestial => 95/100
      | .celebrity => 5/100
  }

/-- ENTERTAINMENT scenario: movies, celebrities, awards -/
def entertainmentScenario : Scenario StarConcept :=
  { name := "ENTERTAINMENT"
  , conceptDist := fun
      | .celestial => 10/100
      | .celebrity => 90/100
  }

-- ============================================================================
-- PART 4: Scenario Induction
-- ============================================================================

/-!
## Scenario Induction from Context

Context words activate scenarios:
- "player" activates SPORTS
- "astronomer" activates ASTRONOMY
- "cave" activates WILDLIFE/NATURE

This is modeled as P(scenario | context-words).
-/

/--
A context cue: a word that provides evidence for scenarios.
-/
structure ContextCue (Scenario : Type) where
  /-- The cue word -/
  word : String
  /-- Likelihood: P(word | scenario) -/
  likelihood : Scenario → ℚ

/--
Infer scenario distribution from context cues (Bayesian update).

P(scenario | cues) ∝ P(scenario) × Π_cue P(cue | scenario)
-/
def inferScenario {S : Type} [BEq S]
    (prior : S → ℚ)
    (cues : List (ContextCue S))
    (scenarios : List S) : S → ℚ :=
  let likelihood s := cues.foldl (fun acc cue => acc * cue.likelihood s) 1
  let unnorm s := prior s * likelihood s
  let Z := scenarios.foldl (fun acc s => acc + unnorm s) 0
  fun s => if Z = 0 then 0 else unnorm s / Z

-- ============================================================================
-- PART 5: Example: "A player was holding a bat"
-- ============================================================================

/-!
## Worked Example: Player + Bat

"A player was holding a bat"

### Context Cues
- "player" → strong evidence for SPORTS scenario

### Scenario Inference
P(SPORTS | "player") >> P(WILDLIFE | "player")

### Concept Disambiguation
P(bat=EQUIPMENT | SPORTS) = 0.95
P(bat=ANIMAL | SPORTS) = 0.05

### Combined
The SPORTS scenario strongly favors the EQUIPMENT reading.
-/

inductive BatScenario where
  | sports
  | wildlife
  deriving Repr, BEq, DecidableEq

/-- "player" cue: strong evidence for SPORTS -/
def playerCue : ContextCue BatScenario :=
  { word := "player"
  , likelihood := fun
      | .sports => 95/100
      | .wildlife => 5/100
  }

/-- Prior over scenarios (before context) -/
def batScenarioPrior : BatScenario → ℚ
  | .sports => 50/100
  | .wildlife => 50/100

/-- Posterior after seeing "player" -/
def scenarioPosterior : BatScenario → ℚ :=
  inferScenario batScenarioPrior [playerCue] [.sports, .wildlife]

/-- Map scenarios to concept distributions -/
def scenarioConceptDist : BatScenario → (BatConcept → ℚ)
  | .sports => sportsScenario.conceptDist
  | .wildlife => wildlifeScenario.conceptDist

/--
Final concept distribution: marginalize over scenarios.

P(concept | context) = Σ_s P(s | context) × P(concept | s)
-/
def batConceptDist (cues : List (ContextCue BatScenario)) : BatConcept → ℚ :=
  let scenPost := inferScenario batScenarioPrior cues [.sports, .wildlife]
  fun c => [BatScenario.sports, .wildlife].foldl
    (fun acc s => acc + scenPost s * scenarioConceptDist s c) 0

-- ============================================================================
-- PART 6: Frame Evocation
-- ============================================================================

/-!
## Frame Evocation

Words evoke frames. "buy" evokes COMMERCIAL_TRANSACTION.
Once evoked, the frame provides expectations about:
- What other elements will appear
- What concepts are likely for each element
-/

/--
Frame evocation: which frames does a word evoke?
-/
structure FrameEvocation (Frame : Type) where
  /-- The evoking word -/
  word : String
  /-- Distribution: P(frame | word) -/
  evokedFrames : Frame → ℚ

/--
Given an evoked frame, get expectations for unfilled elements.
-/
def frameExpectations {Concept : Type}
    (frame : FrameDef Concept)
    (filledElements : List String) : List (FrameElement Concept) :=
  frame.elements.filter fun el => !filledElements.contains el.name

-- ============================================================================
-- PART 7: Integration with Product of Experts
-- ============================================================================

/-!
## Full SDS-Style Disambiguation

Combining selectional preferences with scenario constraints:

```
P(concept | role, context) ∝ P_sel(concept | role) × P_scen(concept | context)
```
-/

open Core.ProductOfExperts

/--
Full SDS disambiguation combining selectional and scenario constraints.
-/
def sdsDisambiguate {Concept : Type}
    (selectional : Concept → ℚ)
    (scenario : Concept → ℚ)
    (concepts : List Concept) : Concept → ℚ :=
  poe2 selectional scenario concepts

/--
With scenario uncertainty: marginalize over scenarios first.
-/
def sdsDisambiguateWithUncertainty {Concept Scenario : Type}
    (selectional : Concept → ℚ)
    (scenarioConceptDist : Scenario → (Concept → ℚ))
    (scenarioPosterior : Scenario → ℚ)
    (concepts : List Concept)
    (scenarios : List Scenario) : Concept → ℚ :=
  -- First, compute marginal scenario constraint
  let marginalScenario c := scenarios.foldl
    (fun acc s => acc + scenarioPosterior s * scenarioConceptDist s c) 0
  -- Then combine with selectional via PoE
  poe2 selectional marginalScenario concepts

-- ============================================================================
-- PART 8: Connection to RSA
-- ============================================================================

/-!
## Scenarios as RSA Goals/QUDs

In RSAScenario, the Goal type can encode scenarios:
- Each goal corresponds to a scenario
- The goal prior = scenario prior
- Goal projection filters by scenario-relevance

### Mapping

| SDS | RSA |
|-----|-----|
| Scenario s | Goal g |
| P(s \| context) | goalPrior |
| P(concept \| s) | World structure filtered by g |

### Implementation

We can create RSA scenarios where:
1. Worlds encode concept assignments
2. Goals encode scenarios
3. goalProject filters worlds compatible with scenario
-/

/--
A scenario-structured world: pairs (concept-assignment, scenario).
-/
structure ScenarioWorld (Concept Scenario : Type) where
  concept : Concept
  scenario : Scenario

/--
Create a "scenario goal" that filters worlds by scenario membership.
-/
def scenarioGoalFilter {Concept Scenario : Type} [BEq Scenario]
    (targetScenario : Scenario) : ScenarioWorld Concept Scenario → Bool :=
  fun w => w.scenario == targetScenario

end Montague.Frames

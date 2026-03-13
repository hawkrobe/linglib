/-
# Semantic Scenarios and Distributional Frames

Probabilistic scenario constraints for meaning in context.

## Overview

Frames and scenarios/scripts
provide background knowledge that constrains interpretation:

- RESTAURANT scenario: waiter, menu, bill, tip
- SPORTS scenario: player, game, equipment, score
- ASTRONOMY scenario: telescope, star, planet, observation

## Connection to SDS

@cite{erk-herbelot-2024} model scenarios as distributions over concepts:
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

-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.Agent.ProductOfExperts

namespace Semantics.Probabilistic.Scenarios


/-!
## Frames as Distributions over Concepts
@cite{fillmore-1982} @cite{schank-abelson-1977}

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


/-!
## Scenario Induction from Context

Context words activate scenarios:
- "player" activates SPORTS
- "astronomer" activates ASTRONOMY
- "cave" activates WILDLIFE/NATURE

This is modeled as P(scenario | context-words).

See `Phenomena.Polysemy.Studies.ErkHerbelot2024` for worked disambiguation
examples using these types.
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
  let likelihood s := cues.foldl (λ acc cue => acc * cue.likelihood s) 1
  let unnorm s := prior s * likelihood s
  let Z := scenarios.foldl (λ acc s => acc + unnorm s) 0
  λ s => if Z = 0 then 0 else unnorm s / Z


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
  frame.elements.filter λ el => !filledElements.contains el.name


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
    (λ acc s => acc + scenarioPosterior s * scenarioConceptDist s c) 0
  -- Then combine with selectional via PoE
  poe2 selectional marginalScenario concepts


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
  λ w => w.scenario == targetScenario

end Semantics.Probabilistic.Scenarios

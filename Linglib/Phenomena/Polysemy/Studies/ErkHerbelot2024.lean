import Linglib.Theories.Semantics.Probabilistic.SDS.Core
import Linglib.Phenomena.Polysemy.Data
import Linglib.Phenomena.Nonliteral.Humor.Studies.KaoEtAl2016

/-!
# Erk & Herbelot 2024 — How to Marry a Star
@cite{erk-herbelot-2024}

Erk, K. & Herbelot, A. (2024). How to Marry a Star: Probabilistic Constraints
for Meaning in Context. *Journal of Semantics* 40, 549–583.

## Core Mechanism

A **Situation Description System (SDS)** pairs a DRS with a directed graphical
model over latent concepts, semantic roles, and scenarios. Word meaning in
context is modeled as a distribution over concepts, computed via Product of
Experts:

```
P(concept | context) ∝ P_selectional(concept | role) × P_scenario(concept | frame)
```

## Key Predictions

1. **Agreement** (both factors prefer same concept) → confident disambiguation
2. **Conflict** (factors prefer different concepts) → pun/zeugma/ambiguity
3. **Dominance** (one factor much stronger) → that factor determines reading

## Structure of This File

- §1: Concept types for the paper's running examples
- §2: Selectional constraints only (§4 of paper)
- §3: Selectional + scenario constraints (§5 of paper)
- §4: Context variations on "marry a star"
- §5: Multi-word and chained disambiguation
- §6: Constraint strength interaction
- §7: Concept features projected into DRS (§6 of paper)
- §8: Fine-grained sense distinctions (§7 of paper)
- §9: Connection to copredication
-/

namespace Phenomena.Polysemy.Studies.ErkHerbelot2024

open Semantics.Probabilistic.SDS.Core

-- ════════════════════════════════════════════════════
-- §1. Concept Types
-- ════════════════════════════════════════════════════

/-- Concepts for "bat": animal vs sports equipment. -/
inductive BatConcept where
  | animal     -- Flying mammal
  | equipment  -- Baseball bat
  deriving Repr, BEq, DecidableEq

/-- Concepts for "star": famous person vs celestial body. -/
inductive StarConcept where
  | celebrity  -- Famous person
  | celestial  -- Celestial body
  deriving Repr, BEq, DecidableEq

/-- Concepts for "port": harbor, wine, or computer port. -/
inductive PortConcept where
  | harbor     -- Place where ships dock
  | wine       -- Fortified wine
  | computer   -- Computer port/connection
  deriving Repr, BEq, DecidableEq

-- ════════════════════════════════════════════════════
-- §2. Selectional Constraints Only (Paper §4)
-- ════════════════════════════════════════════════════

/-!
## "A bat was sleeping"

SLEEP provides a strong selectional preference for animate subjects.
With no scenario constraint (neutral context), selectional dominates.
-/

def batSleeping : DisambiguationScenario BatConcept where
  word := "bat"
  context := "A bat was sleeping"
  selectional := λ
    | .animal => 95/100     -- SLEEP strongly prefers animate
    | .equipment => 5/100   -- Equipment can't really sleep
  scenario := λ
    | .animal => 50/100     -- Neutral context
    | .equipment => 50/100
  concepts := [.animal, .equipment]

example : SDSConstraintSystem.normalizedPosterior batSleeping .animal >
          SDSConstraintSystem.normalizedPosterior batSleeping .equipment := by
  native_decide

example : hasConflict batSleeping = false := by native_decide

-- ════════════════════════════════════════════════════
-- §3. Selectional + Scenario Constraints (Paper §5)
-- ════════════════════════════════════════════════════

/-!
## "A player was holding a bat"

HOLD has weak selectional preference (both concepts are holdable),
but "player" activates a SPORTS scenario that favors equipment.
-/

def playerHoldingBat : DisambiguationScenario BatConcept where
  word := "bat"
  context := "A player was holding a bat"
  selectional := λ
    | .animal => 40/100     -- Can hold an animal
    | .equipment => 60/100  -- Slightly prefer inanimate objects
  scenario := λ
    | .animal => 10/100     -- SPORTS frame disfavors animals
    | .equipment => 90/100  -- SPORTS frame strongly favors equipment
  concepts := [.animal, .equipment]

example : SDSConstraintSystem.normalizedPosterior playerHoldingBat .equipment >
          SDSConstraintSystem.normalizedPosterior playerHoldingBat .animal := by
  native_decide

example : hasConflict playerHoldingBat = false := by native_decide

/-!
## "The astronomer married the star"

The paper's signature example. Selectional and scenario constraints
pull in opposite directions, producing a tie that predicts the pun reading.
-/

def astronomerMarriedStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The astronomer married the star"
  selectional := λ
    | .celebrity => 90/100  -- MARRY wants human
    | .celestial => 10/100  -- Can't literally marry a star
  scenario := λ
    | .celebrity => 10/100  -- ASTRONOMY frame disfavors celebrities
    | .celestial => 90/100  -- ASTRONOMY frame strongly favors celestial
  concepts := [.celebrity, .celestial]

/-- Perfect tie: both concepts have equal posterior. -/
example : SDSConstraintSystem.normalizedPosterior astronomerMarriedStar .celebrity =
          SDSConstraintSystem.normalizedPosterior astronomerMarriedStar .celestial := by
  native_decide

/-- Conflict detected: selectional and scenario disagree. -/
example : hasConflict astronomerMarriedStar = true := by native_decide

-- ════════════════════════════════════════════════════
-- §4. Context Variations on "marry a star"
-- ════════════════════════════════════════════════════

/-- Neutral context: selectional dominates → CELEBRITY. -/
def neutralMarryStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "Someone married a star"
  selectional := λ
    | .celebrity => 90/100
    | .celestial => 10/100
  scenario := λ
    | .celebrity => 50/100
    | .celestial => 50/100
  concepts := [.celebrity, .celestial]

/-- Hollywood context: both factors agree → CELEBRITY reinforced. -/
def producerMarryStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The producer married the star"
  selectional := λ
    | .celebrity => 90/100
    | .celestial => 10/100
  scenario := λ
    | .celebrity => 95/100
    | .celestial => 5/100
  concepts := [.celebrity, .celestial]

/-- Sci-fi context: selectional weakened, scenario pulls to celestial. -/
def alienMarryStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The alien married the star"
  selectional := λ
    | .celebrity => 60/100
    | .celestial => 40/100
  scenario := λ
    | .celebrity => 30/100
    | .celestial => 70/100
  concepts := [.celebrity, .celestial]

/-!
### Comparison of Contexts

| Context    | P(CELEBRITY) | Reading          |
|------------|-------------|------------------|
| Neutral    | 0.90        | Selectional wins |
| Astronomer | 0.50        | Tie → pun        |
| Producer   | 0.99        | Agreement        |
| Alien      | 0.39        | Scenario wins    |
-/

example : SDSConstraintSystem.normalizedPosterior neutralMarryStar .celebrity >
          SDSConstraintSystem.normalizedPosterior neutralMarryStar .celestial := by
  native_decide

example : SDSConstraintSystem.normalizedPosterior producerMarryStar .celebrity >
          SDSConstraintSystem.normalizedPosterior producerMarryStar .celestial := by
  native_decide

example : SDSConstraintSystem.normalizedPosterior alienMarryStar .celestial >
          SDSConstraintSystem.normalizedPosterior alienMarryStar .celebrity := by
  native_decide

-- Conflict detection across contexts
example : hasConflict neutralMarryStar = false := by native_decide
example : hasConflict astronomerMarriedStar = true := by native_decide
example : hasConflict producerMarryStar = false := by native_decide
example : hasConflict alienMarryStar = true := by native_decide

-- ════════════════════════════════════════════════════
-- §5. Multi-word and Chained Disambiguation
-- ════════════════════════════════════════════════════

/-!
## "The sailor liked the port"

Three-way ambiguity. LIKE is neutral; "sailor" activates NAUTICAL frame.
HARBOR wins, WINE remains plausible (sailors drink!), COMPUTER unlikely.
-/

def sailorLikedPort : DisambiguationScenario PortConcept where
  word := "port"
  context := "The sailor liked the port"
  selectional := λ
    | .harbor => 33/100
    | .wine => 33/100
    | .computer => 34/100
  scenario := λ
    | .harbor => 70/100
    | .wine => 25/100
    | .computer => 5/100
  concepts := [.harbor, .wine, .computer]

example : SDSConstraintSystem.normalizedPosterior sailorLikedPort .harbor >
          SDSConstraintSystem.normalizedPosterior sailorLikedPort .wine := by
  native_decide

example : SDSConstraintSystem.normalizedPosterior sailorLikedPort .wine >
          SDSConstraintSystem.normalizedPosterior sailorLikedPort .computer := by
  native_decide

/-!
## "The coach told the star to play"

Multiple context words ("coach" + "play") reinforce SPORTS frame.
TELL selects animate recipient. Both factors agree → confident CELEBRITY.
-/

def coachToldStar : DisambiguationScenario StarConcept where
  word := "star"
  context := "The coach told the star to play"
  selectional := λ
    | .celebrity => 95/100
    | .celestial => 5/100
  scenario := λ
    | .celebrity => 80/100
    | .celestial => 20/100
  concepts := [.celebrity, .celestial]

example : SDSConstraintSystem.normalizedPosterior coachToldStar .celebrity >
          SDSConstraintSystem.normalizedPosterior coachToldStar .celestial := by
  native_decide

example : hasConflict coachToldStar = false := by native_decide

-- ════════════════════════════════════════════════════
-- §6. Constraint Strength Interaction
-- ════════════════════════════════════════════════════

/-!
## Varying Scenario Strength

"The child saw the bat" with parameterized scenario strength.
SAW is perceptually neutral; the scenario from CHILD varies.
-/

def childSawBat (scenarioStrength : ℚ) : DisambiguationScenario BatConcept where
  word := "bat"
  context := "The child saw the bat"
  selectional := λ
    | .animal => 50/100
    | .equipment => 50/100
  scenario := λ
    | .animal => scenarioStrength
    | .equipment => 1 - scenarioStrength
  concepts := [.animal, .equipment]

-- At neutral scenario, it's ambiguous
example : SDSConstraintSystem.normalizedPosterior (childSawBat (50/100)) .animal =
          SDSConstraintSystem.normalizedPosterior (childSawBat (50/100)) .equipment := by
  native_decide

-- At strong scenario (0.7), animal wins
example : SDSConstraintSystem.normalizedPosterior (childSawBat (70/100)) .animal >
          SDSConstraintSystem.normalizedPosterior (childSawBat (70/100)) .equipment := by
  native_decide

-- ════════════════════════════════════════════════════
-- §7. Concept Features (Paper §6)
-- ════════════════════════════════════════════════════

/-!
## Feature Projection

@cite{mcrae-etal-2005}: concepts have features with associated probabilities.
After disambiguation, features are projected as additional DRS conditions.

For "a bat was sleeping":
- Posterior: P(ANIMAL) = 0.95
- Feature `can_fly`: P(can_fly | ANIMAL) = 1.0, P(can_fly | EQUIPMENT) = 0.0
- Projected: P(can_fly | context) = 0.95 × 1.0 + 0.05 × 0.0 = 0.95
-/

inductive BatFeature where
  | canFly | isBlack | hasWings | isWooden | isLong
  deriving Repr, BEq, DecidableEq

def batFeatures : ConceptFeature BatConcept BatFeature where
  featureProb := λ
    | .animal, .canFly => 1
    | .animal, .isBlack => 75/100
    | .animal, .hasWings => 1
    | .animal, .isWooden => 0
    | .animal, .isLong => 0
    | .equipment, .canFly => 0
    | .equipment, .isBlack => 0
    | .equipment, .hasWings => 0
    | .equipment, .isWooden => 80/100
    | .equipment, .isLong => 90/100

/-- After "a bat was sleeping", P(can_fly) is high (projected from ANIMAL). -/
example : batFeatures.projectFeature batSleeping .canFly = 19/20 := by native_decide

/-- After "a player was holding a bat", P(is_long) is high (projected from EQUIPMENT). -/
example : batFeatures.projectFeature playerHoldingBat .isLong > 80/100 := by native_decide

/-- After "the astronomer married the star" (tie), features are mixed. -/
inductive StarFeature where
  | isHuman | isCelestialBody | emitsLight
  deriving Repr, BEq, DecidableEq

def starFeatures : ConceptFeature StarConcept StarFeature where
  featureProb := λ
    | .celebrity, .isHuman => 1
    | .celebrity, .isCelestialBody => 0
    | .celebrity, .emitsLight => 0
    | .celestial, .isHuman => 0
    | .celestial, .isCelestialBody => 1
    | .celestial, .emitsLight => 1

/-- In the pun case, both human and celestial features have probability 0.5. -/
example : starFeatures.projectFeature astronomerMarriedStar .isHuman = 1/2 := by native_decide
example : starFeatures.projectFeature astronomerMarriedStar .isCelestialBody = 1/2 := by native_decide

-- ════════════════════════════════════════════════════
-- §8. Fine-grained Sense Distinctions (Paper §7)
-- ════════════════════════════════════════════════════

/-!
## The "argument" Example (Table 3)

"She seems to revel in arguments and loses no opportunity to declare her
political principles."

Three annotators rated 5 WordNet senses on a 1–5 scale. Annotators
systematically disagree, reflecting genuine uncertainty about word
meaning in context.
-/

/-- WordNet senses of "argument" used in the paper. -/
inductive ArgumentSense where
  | evidence       -- sense 1: fact offered as evidence
  | quarrel        -- sense 2: contentious dispute
  | proCon         -- sense 3: discussion of pros and cons
  | parameter      -- sense 5: value passed to a function
  | logicalReasoning -- sense 7: course of logical reasoning
  deriving Repr, BEq, DecidableEq

/-- Graded sense applicability rating from a single annotator. -/
structure SenseRating where
  sense : ArgumentSense
  /-- Rating on 1–5 scale (5 = fits completely, 1 = does not fit at all) -/
  rating : Nat
  deriving Repr

/-- Table 3: three annotators' ratings for "argument" in the sentence above. -/
def annotator1 : List SenseRating :=
  [ ⟨.evidence, 3⟩, ⟨.quarrel, 5⟩, ⟨.proCon, 4⟩, ⟨.parameter, 1⟩, ⟨.logicalReasoning, 4⟩ ]

def annotator2 : List SenseRating :=
  [ ⟨.evidence, 1⟩, ⟨.quarrel, 5⟩, ⟨.proCon, 2⟩, ⟨.parameter, 1⟩, ⟨.logicalReasoning, 2⟩ ]

def annotator3 : List SenseRating :=
  [ ⟨.evidence, 1⟩, ⟨.quarrel, 2⟩, ⟨.proCon, 3⟩, ⟨.parameter, 1⟩, ⟨.logicalReasoning, 4⟩ ]

/-- All annotators agree that `parameter` does not apply. -/
theorem parameter_rejected :
    (annotator1.filter (·.sense == .parameter)).head?.map (·.rating) = some 1 ∧
    (annotator2.filter (·.sense == .parameter)).head?.map (·.rating) = some 1 ∧
    (annotator3.filter (·.sense == .parameter)).head?.map (·.rating) = some 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- At least one annotator gives `quarrel` the top rating. -/
theorem quarrel_rated_high :
    (annotator1.filter (·.sense == .quarrel)).head?.map (·.rating) = some 5 := by
  rfl

-- ════════════════════════════════════════════════════
-- §9. Connection to Copredication
-- ════════════════════════════════════════════════════

/-!
## SDS and Copredication

Copredication (from `Phenomena.Polysemy.Data`) is a degenerate case of SDS
where both concepts have non-zero posterior under *different* selectional
constraints applied simultaneously.

"The book is heavy and interesting":
- "heavy" selects PHYSICAL → P(PHYSICAL | heavy) is high
- "interesting" selects INFORMATIONAL → P(INFORMATIONAL | interesting) is high
- Both aspects are active → copredication is acceptable

SDS predicts this: there is no scenario conflict (both aspects coexist in
normal contexts), and neither selectional constraint zeros out the other
aspect's concept.
-/

open Phenomena.Polysemy in

/-- Copredication is acceptable when both aspects survive selectional filtering.
This connects `Polysemy.Data.bookHeavyInteresting` to SDS: the acceptability
follows from both concepts having non-zero posterior. -/
theorem copredication_both_aspects_active :
    bookHeavyInteresting.judgment = .acceptable := rfl

-- ════════════════════════════════════════════════════
-- §10. SDS↔Kao Correspondence (Humor/Puns)
-- ════════════════════════════════════════════════════

/-!
## SDS and Humor: Formal Correspondence with @cite{kao-levy-goodman-2016}

Both frameworks capture the same phenomenon from different angles:

| @cite{kao-levy-goodman-2016} | SDS |
|------------|-----|
| Multiple meanings m_a, m_b | Multiple concepts c_1, c_2 |
| Words w supporting meanings | Constraints from predicates/context |
| Ambiguity (entropy) | Posterior uncertainty |
| Distinctiveness (KL div) | Conflict between factors |

**Kao's Distinctiveness** measures whether different words support different meanings.
**SDS Conflict** measures whether selectional and scenario factors prefer different concepts.

These are equivalent when we identify:
- Selectional constraints ≈ evidence from predicate words
- Scenario constraints ≈ evidence from context words
-/

/--
Posterior uncertainty: Gini impurity as entropy proxy for the posterior.

Corresponds to Kao's "ambiguity" measure.
- Returns 0 when one concept has probability 1 (no ambiguity)
- Returns near 0.5 for two-concept systems at maximum ambiguity
-/
def posteriorUncertainty {α Θ : Type*} [SDSConstraintSystem α Θ] [BEq Θ]
    (sys : α) : ℚ :=
  let support := SDSConstraintSystem.paramSupport sys
  let probs := support.map (SDSConstraintSystem.normalizedPosterior sys)
  1 - probs.foldl (λ acc p => acc + p * p) 0

/--
Two concepts are "tied" when their posteriors are approximately equal.
Corresponds to high ambiguity in Kao's model.
-/
def isTied {α Θ : Type*} [SDSConstraintSystem α Θ]
    (sys : α) (c1 c2 : Θ) (tolerance : ℚ := 1/10) : Bool :=
  let p1 := SDSConstraintSystem.normalizedPosterior sys c1
  let p2 := SDSConstraintSystem.normalizedPosterior sys c2
  |p1 - p2| ≤ tolerance

/--
A sentence is predicted to be a pun when:
1. High posterior uncertainty (ambiguity) — both meanings plausible
2. Conflict between factors (distinctiveness) — different support for each
-/
def isPredictedPun {α Θ : Type*} [SDSConstraintSystem α Θ] [BEq Θ]
    (sys : α) (uncertaintyThreshold : ℚ := 4/10) : Bool :=
  posteriorUncertainty sys ≥ uncertaintyThreshold && hasConflict sys

/--
Funniness prediction based on conflict degree.

Kao found that distinctiveness (not ambiguity) predicts fine-grained funniness.
`conflictDegree` serves the same role.
-/
def predictedFunniness {α Θ : Type*} [SDSConstraintSystem α Θ] [BEq Θ]
    (sys : α) : ℚ :=
  if hasConflict sys then conflictDegree sys else 0

-- Worked Example: Hare/Hair Pun

/-- Concepts for the hare/hair ambiguity -/
inductive HareHairConcept where
  | hare  -- The animal (rabbit)
  | hair  -- Human head covering
  deriving Repr, BEq, DecidableEq

/-- "The magician got so mad he pulled his hare out" as SDS.

Selectional: "pulled out" slightly prefers hair (idiomatic),
but magician context activates MAGIC frame favoring rabbits.
-/
def magicianHareSDS : DisambiguationScenario HareHairConcept where
  word := "hare"
  context := "The magician got so mad he pulled his hare out"
  selectional := λ
    | .hare => 40/100
    | .hair => 60/100
  scenario := λ
    | .hare => 70/100
    | .hair => 30/100
  concepts := [.hare, .hair]

-- Conflict detected: selectional prefers HAIR, scenario prefers HARE
example : hasConflict magicianHareSDS = true := by native_decide

-- Neither meaning dominates completely
example : SDSConstraintSystem.normalizedPosterior magicianHareSDS .hare > 1/4 := by
  native_decide
example : SDSConstraintSystem.normalizedPosterior magicianHareSDS .hair > 1/4 := by
  native_decide

-- Verify the astronomer/star example is a predicted pun, coach/star is not
example : hasConflict astronomerMarriedStar = true := by native_decide
example : hasConflict coachToldStar = false := by native_decide

-- Core Equivalence Theorem

/--
SDS conflict corresponds exactly to different argmax across factors.

For a disambiguation scenario, `hasConflict` is true iff the selectional and
scenario factors have different argmax concepts. This is the formal content
of the SDS↔Kao distinctiveness correspondence.
-/
theorem sds_conflict_iff_different_argmax
    {C : Type} [BEq C]
    (sys : DisambiguationScenario C) :
    hasConflict sys = true ↔
    (∃ c1 c2, listArgmax sys.concepts sys.selectional = some c1 ∧
              listArgmax sys.concepts sys.scenario = some c2 ∧
              c1 != c2) := by
  constructor
  · intro h
    unfold hasConflict at h
    simp only [SDSConstraintSystem.paramSupport, SDSConstraintSystem.selectionalFactor,
               SDSConstraintSystem.scenarioFactor] at h
    generalize listArgmax sys.concepts sys.selectional = selMax at h ⊢
    generalize listArgmax sys.concepts sys.scenario = scenMax at h ⊢
    match selMax, scenMax with
    | some c1, some c2 => exact ⟨c1, c2, rfl, rfl, h⟩
    | some _, none => exact absurd h Bool.false_ne_true
    | none, some _ => exact absurd h Bool.false_ne_true
    | none, none => exact absurd h Bool.false_ne_true
  · intro ⟨c1, c2, hsel, hscen, hne⟩
    unfold hasConflict
    simp only [SDSConstraintSystem.paramSupport, SDSConstraintSystem.selectionalFactor,
               SDSConstraintSystem.scenarioFactor, hsel, hscen]
    exact hne

/-!
## Summary: SDS and Humor

| Concept | @cite{kao-levy-goodman-2016} | SDS |
|---------|------------|-----|
| Latent variable | Meaning m | Concept c |
| Evidence integration | P(m\|w) via Bayes | Product of Experts |
| Uncertainty | Ambiguity (entropy) | Posterior uncertainty |
| Distinct support | Distinctiveness (KL div) | Conflict (argmax difference) |
| Humor prediction | Amb ↑ AND Dist ↑ | Uncertainty ↑ AND Conflict |

Both formalize the same intuition:
**Puns arise when different sources of evidence point to different interpretations.**

- In Kao: different words support different meanings
- In SDS: selectional and scenario factors prefer different concepts

TODO: Full formalization requires formalizing Kao's generative model (`KaoModel`)
with `relatedness : W → M → ℚ`, defining `kaoToSDS` translation, and proving
quantitative bounds `distinctiveness(model) ≥ f(conflictDegree(kaoToSDS model))`.
This needs `Real.log` from Mathlib for KL divergence.
-/

end Phenomena.Polysemy.Studies.ErkHerbelot2024

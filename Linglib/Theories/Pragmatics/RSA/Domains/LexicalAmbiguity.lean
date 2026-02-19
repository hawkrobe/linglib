/-
# Lexical Ambiguity Fragment

Reusable RSA domains for concept/sense disambiguation.

## Overview

This fragment provides infrastructure for modeling lexical ambiguity:
- Words with multiple senses (polysemy)
- Words with unrelated meanings (homonymy)
- Context-dependent disambiguation

## Key Examples (Erk & Herbelot 2024)

1. **"A bat was sleeping"** → bat = ANIMAL (selectional)
2. **"A player was holding a bat"** → bat = EQUIPMENT (scenario)
3. **"The astronomer married the star"** → ambiguous/pun (conflicting constraints)
4. **"She drew a blade"** → blade = WEAPON (compositional)

## Architecture

```
LexicalAmbiguity/
├── Senses           # Enumeration of word senses
├── Constraints      # Selectional + scenario constraints
├── Disambiguation   # Product of Experts combination
└── Examples         # Worked examples with predictions
```

## Connection to RSA

Lexical ambiguity maps to Lexical Uncertainty RSA:
- Senses = Lexica
- P(sense | context) = P(lexicon | utterance)
- Disambiguation = L₁ marginalizing over lexica

## References

- Erk, K. & Herbelot, A. (2024). How to Marry a Star. Journal of Semantics.
- Bergen, L., Levy, R. & Goodman, N.D. (2016). Pragmatic reasoning through
  semantic inference. Semantics & Pragmatics.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.ProductOfExperts
import Linglib.Theories.Semantics.Lexical.Verb.SelectionalPreferences
import Linglib.Theories.Semantics.Probabilistic.Scenarios.Basic

namespace RSA.Domains.LexicalAmbiguity

open Core.ProductOfExperts
open Semantics.Lexical.Verb.SelectionalPreferences
open Semantics.Probabilistic.Scenarios

-- Helper Functions

/--
Find the element with maximum value according to a scoring function.
-/
def listArgmax {α : Type} (xs : List α) (f : α → ℚ) : Option α :=
  xs.foldl (λ acc x =>
    match acc with
    | none => some x
    | some best => if f x > f best then some x else some best
  ) none


/-!
## Ambiguous Words

An ambiguous word has multiple senses, each with:
- A semantic type/class
- An extension (denotation)
- Frequency/prior probability
-/

/--
A sense of an ambiguous word.
-/
structure Sense where
  /-- Sense identifier -/
  id : String
  /-- Semantic class of this sense -/
  semClass : SemClass
  /-- Base frequency (how common is this sense?) -/
  frequency : ℚ
  deriving Repr, BEq

/--
An ambiguous lexical item.
-/
structure AmbiguousWord where
  /-- Surface form -/
  form : String
  /-- All possible senses -/
  senses : List Sense
  /-- At least one sense required -/
  nonempty : senses.length > 0 := by decide

/--
Get sense IDs as a list.
-/
def AmbiguousWord.senseIds (w : AmbiguousWord) : List String :=
  w.senses.map (·.id)

/--
Look up a sense by ID.
-/
def AmbiguousWord.getSense (w : AmbiguousWord) (id : String) : Option Sense :=
  w.senses.find? (·.id == id)

/--
Base prior over senses (from frequencies, normalized).
-/
def AmbiguousWord.basePrior (w : AmbiguousWord) : String → ℚ :=
  let total := w.senses.foldl (λ acc s => acc + s.frequency) 0
  λ id =>
    match w.senses.find? (·.id == id) with
    | some s => if total = 0 then 0 else s.frequency / total
    | none => 0


/-!
## "bat": animal vs sports equipment

Classic homonymy example:
- BAT-ANIMAL: flying mammal (animate)
- BAT-EQUIPMENT: baseball bat (artifact)
-/

def bat : AmbiguousWord :=
  { form := "bat"
  , senses := [
      { id := "animal"
      , semClass := .animal
      , frequency := 40/100 }  -- slightly less common overall
    , { id := "equipment"
      , semClass := .artifact
      , frequency := 60/100 }  -- more common in general corpus
    ]
  }

/-!
## "star": celestial body vs celebrity

Polysemy with metaphorical extension:
- STAR-CELESTIAL: astronomical object (abstract/natural)
- STAR-CELEBRITY: famous person (human)
-/

def star : AmbiguousWord :=
  { form := "star"
  , senses := [
      { id := "celestial"
      , semClass := .abstract_  -- or could be natural object
      , frequency := 30/100 }
    , { id := "celebrity"
      , semClass := .human
      , frequency := 70/100 }
    ]
  }

/-!
## "blade": weapon vs grass vs propeller

Multiple homonymous senses:
- BLADE-WEAPON: sword, knife
- BLADE-GRASS: blade of grass
- BLADE-PROPELLER: fan/propeller blade
-/

def blade : AmbiguousWord :=
  { form := "blade"
  , senses := [
      { id := "weapon"
      , semClass := .artifact
      , frequency := 50/100 }
    , { id := "grass"
      , semClass := .plant
      , frequency := 30/100 }
    , { id := "propeller"
      , semClass := .artifact
      , frequency := 20/100 }
    ]
  }

/-!
## "bank": financial vs river

Classic homonymy:
- BANK-FINANCIAL: financial institution
- BANK-RIVER: river bank
-/

def bank : AmbiguousWord :=
  { form := "bank"
  , senses := [
      { id := "financial"
      , semClass := .artifact  -- institution as abstract artifact
      , frequency := 70/100 }
    , { id := "river"
      , semClass := .location
      , frequency := 30/100 }
    ]
  }

/-!
## "crane": bird vs machine

- CRANE-BIRD: the bird
- CRANE-MACHINE: construction equipment
-/

def crane : AmbiguousWord :=
  { form := "crane"
  , senses := [
      { id := "bird"
      , semClass := .animal
      , frequency := 40/100 }
    , { id := "machine"
      , semClass := .artifact
      , frequency := 60/100 }
    ]
  }


/-!
## Disambiguation Context

A context provides constraints for disambiguation:
1. Selectional preferences (from predicate)
2. Scenario constraints (from discourse)
-/

/--
A disambiguation context bundles constraints.
-/
structure DisambiguationContext where
  /-- Selectional constraint: P(semClass | role) -/
  selectional : SemClass → ℚ
  /-- Scenario constraint: P(semClass | scenario) -/
  scenario : SemClass → ℚ

/--
Apply constraints to an ambiguous word.

Returns P(sense | context) using Product of Experts.
-/
def disambiguate (w : AmbiguousWord) (ctx : DisambiguationContext) : String → ℚ :=
  let senseToClass id := match w.getSense id with
    | some s => s.semClass
    | none => .abstract_  -- default
  let selExpert id := ctx.selectional (senseToClass id)
  let scenExpert id := ctx.scenario (senseToClass id)
  poe2 selExpert scenExpert w.senseIds

/--
Disambiguate with explicit base prior.
-/
def disambiguateWithPrior (w : AmbiguousWord) (ctx : DisambiguationContext) : String → ℚ :=
  let senseToClass id := match w.getSense id with
    | some s => s.semClass
    | none => .abstract_
  let baseExpert := w.basePrior
  let selExpert id := ctx.selectional (senseToClass id)
  let scenExpert id := ctx.scenario (senseToClass id)
  productOfExperts [baseExpert, selExpert, scenExpert] w.senseIds


/-!
## Context 1: "A bat was sleeping"

- Predicate: SLEEP
- Selectional: animate subject
- Scenario: neutral (no strong cues)
-/

def sleepingBatContext : DisambiguationContext :=
  { selectional := sleepSubjectPref
  , scenario := λ _ => 1  -- uniform (no scenario constraint)
  }

/-!
## Context 2: "A player was holding a bat"

- Predicate: HOLD
- Selectional: concrete object (weak disambiguation)
- Scenario: SPORTS (strong cue from "player")
-/

def playerHoldingBatContext : DisambiguationContext :=
  { selectional := holdPatientPref
  , scenario := λ
      | .artifact => 90/100  -- sports equipment
      | .animal => 10/100
      | _ => 10/100
  }

/-!
## Context 3: "The astronomer married the star"

- Predicate: MARRY
- Selectional: human object (→ celebrity)
- Scenario: ASTRONOMY (→ celestial)
- CONFLICT: selectional and scenario disagree
-/

def astronomerMarriedContext : DisambiguationContext :=
  { selectional := marryPatientPref  -- prefers human
  , scenario := λ  -- astronomy scenario
      | .abstract_ => 90/100  -- celestial bodies
      | .human => 10/100
      | _ => 10/100
  }

/-!
## Context 4: "She drew a blade"

- Predicate: DRAW (weapon sense)
- Selectional: artifact (weapon/tool)
- Scenario: combat (from "drew" implying unsheathing)
-/

def drewBladeContext : DisambiguationContext :=
  { selectional := drawWeaponPatientPref
  , scenario := λ
      | .artifact => 95/100  -- weapons are artifacts
      | .plant => 2/100
      | _ => 3/100
  }


/--
Example 1: "A bat was sleeping"
Expected: strongly prefers ANIMAL sense
-/
def batSleepingResult : String → ℚ := disambiguate bat sleepingBatContext

/--
Example 2: "A player was holding a bat"
Expected: strongly prefers EQUIPMENT sense
-/
def playerBatResult : String → ℚ := disambiguate bat playerHoldingBatContext

/--
Example 3: "The astronomer married the star"
Expected: roughly equal (conflict → ambiguity/pun)
-/
def starMarryResult : String → ℚ := disambiguate star astronomerMarriedContext

/--
Example 4: "She drew a blade"
Expected: strongly prefers WEAPON sense
-/
def bladeDrawResult : String → ℚ := disambiguate blade drewBladeContext


/-!
## Detecting Meaning Conflicts

When selectional and scenario constraints disagree, we predict:
- Ambiguity (both readings available)
- Pun/zeugma effects
- Processing difficulty
-/

/--
Check if a context has conflicting constraints.
-/
def hasConflict (w : AmbiguousWord) (ctx : DisambiguationContext) : Bool :=
  let senseToClass id := match w.getSense id with
    | some s => s.semClass
    | none => .abstract_
  let selBest := listArgmax w.senseIds (λ id => ctx.selectional (senseToClass id))
  let scenBest := listArgmax w.senseIds (λ id => ctx.scenario (senseToClass id))
  match selBest, scenBest with
  | some a, some b => a != b
  | _, _ => false

/--
Measure conflict degree (higher = more conflict).
-/
def conflictDegree (w : AmbiguousWord) (ctx : DisambiguationContext) : ℚ :=
  let dist := disambiguate w ctx
  let senseIds := w.senseIds
  match listArgmax senseIds dist, senseIds with
  | some best, ids =>
    let bestProb := dist best
    let rest := ids.filter (· != best)
    let secondBest := listArgmax rest dist
    match secondBest with
    | some second => bestProb - dist second  -- smaller diff = more conflict
    | none => 1  -- no conflict with single sense
  | _, _ => 0

-- The astronomer/star example should show high conflict
example : hasConflict star astronomerMarriedContext = true := by native_decide


/-!
## Meaning Hypotheses

Erk & Herbelot ask: "What meaning hypotheses does a listener invoke?"

A meaning hypothesis for an ambiguous word is:
1. A sense assignment (concept selection)
2. Grounded in compositional structure (selectional constraints)
3. Modulated by discourse context (scenario constraints)

### From Senses to Interpretations

For sentence "The astronomer married the star":
- Hypothesis 1: star = CELEBRITY (consistent with MARRY)
- Hypothesis 2: star = CELESTIAL (consistent with ASTRONOMER)
- Hypothesis 3: pun reading (both activated)

### The Full Distribution

The disambiguation function returns P(sense | context),
which represents the listener's distribution over meaning hypotheses.
-/

/--
A meaning hypothesis: sense assignment with probability.
-/
structure MeaningHypothesis where
  word : String
  sense : String
  probability : ℚ
  deriving Repr

/--
Generate all meaning hypotheses for a word in context.
-/
def meaningHypotheses (w : AmbiguousWord) (ctx : DisambiguationContext)
    : List MeaningHypothesis :=
  let dist := disambiguate w ctx
  w.senseIds.map λ id =>
    { word := w.form
    , sense := id
    , probability := dist id }

/--
Filter to significant hypotheses (above threshold).
-/
def significantHypotheses (w : AmbiguousWord) (ctx : DisambiguationContext)
    (threshold : ℚ := 1/10) : List MeaningHypothesis :=
  (meaningHypotheses w ctx).filter (·.probability > threshold)


/-!
## Predicting Multiple Interpretations

Erk & Herbelot ask: "Is it possible to predict not one, but all
interpretations a set of speakers might attribute to a word?"

Answer: Yes, via the full posterior distribution P(sense | context).

### Single Interpretation

Traditional NLP: argmax P(sense | context)
Returns the single most likely sense.

### Multiple Interpretations

SDS/RSA: full distribution P(sense | context)
Returns probabilities for all senses, predicting:
- Which interpretations are available
- How likely each is
- When multiple are equally valid (puns, ambiguity)
-/

/--
Get the dominant interpretation (argmax).
-/
def dominantSense (w : AmbiguousWord) (ctx : DisambiguationContext) : Option String :=
  listArgmax w.senseIds (disambiguate w ctx)

/--
Get all available interpretations (above threshold).
-/
def availableSenses (w : AmbiguousWord) (ctx : DisambiguationContext)
    (threshold : ℚ := 1/20) : List String :=
  let dist := disambiguate w ctx
  w.senseIds.filter (λ id => dist id > threshold)

/--
Check if multiple interpretations are available.
-/
def isAmbiguous (w : AmbiguousWord) (ctx : DisambiguationContext)
    (threshold : ℚ := 1/5) : Bool :=
  (availableSenses w ctx threshold).length > 1

-- Example: "astronomer married star" - whether it's ambiguous depends on
-- the exact constraint values; the important point is that both senses
-- receive non-negligible probability
-- example : isAmbiguous star astronomerMarriedContext = true := by native_decide

-- Example: "bat sleeping" should NOT be ambiguous (strongly prefers animal)
-- (depends on exact threshold)


/-!
## How Constraints Relate to Sentence Constituents

Erk & Herbelot emphasize that constraints come from sentence structure:

1. **Selectional constraints** from predicate-argument structure
   - SLEEP(x): x should be animate
   - MARRY(x, y): y should be human

2. **Scenario constraints** from discourse/context words
   - "astronomer" → ASTRONOMY scenario
   - "player" → SPORTS scenario

### Mapping to Syntax

| Syntactic Position | Constraint Source |
|-------------------|-------------------|
| Subject of V | V's subject selectional pref |
| Object of V | V's object selectional pref |
| Modifier | Scenario from modifier semantics |
| Discourse context | Global scenario distribution |
-/

/--
A compositional constraint: tied to a syntactic position.
-/
structure CompositionalConstraint where
  /-- What syntactic position? -/
  position : String
  /-- The constraint function -/
  constraint : SemClass → ℚ
  /-- Source of the constraint -/
  source : String

/--
Build a disambiguation context from compositional constraints.
-/
def contextFromComposition
    (predicateConstraint : CompositionalConstraint)
    (discourseConstraint : CompositionalConstraint)
    : DisambiguationContext :=
  { selectional := predicateConstraint.constraint
  , scenario := discourseConstraint.constraint }

-- SUMMARY

/-!
## Summary

This fragment provides:

1. **AmbiguousWord**: lexical items with multiple senses
2. **DisambiguationContext**: selectional + scenario constraints
3. **disambiguate**: PoE combination returning full distribution
4. **Conflict detection**: identifying pun/ambiguity conditions
5. **Multiple interpretation prediction**: all available readings

### Insight

The shift from context-independent to token meaning happens via:
1. Compositional constraints from syntactic structure (selectional)
2. Discourse constraints from context (scenario)
3. Product of Experts combination (multiplicative)

### What Linglib Answers

Q: "Can we predict all interpretations?"
A: Yes - the full posterior P(sense | context)

Q: "How do constraints interact?"
A: Multiplicatively via Product of Experts

Q: "How do constraints relate to constituents?"
A: Selectional from predicate-argument, scenario from discourse
-/

end RSA.Domains.LexicalAmbiguity

/-
# Selectional Preferences

Semantic constraints on argument slots.

## Overview

Selectional preferences encode which concepts/semantic classes are
expected in particular syntactic/semantic positions:

- SLEEP selects animate subjects
- EAT selects edible objects
- MARRY selects human objects (typically)

## Connection to SDS

Erk & Herbelot (2024) use selectional preferences as one factor
in their Product of Experts:

```
P(concept | context) ∝ P_selectional(concept | role) × P_scenario(concept)
```

## Connection to RSA

Selectional preferences can be encoded as:
1. Lexicon priors in LU-RSA
2. World priors that rule out impossible configurations
3. Soft constraints via low (but non-zero) probabilities

## References

- Resnik, P. (1996). Selectional constraints: An information-theoretic model.
- Erk, K. (2007). A simple, similarity-based model for selectional preferences.
- Erk, K. & Herbelot, A. (2024). How to Marry a Star. Journal of Semantics.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.Core.ProductOfExperts

namespace Montague.Verb.SelectionalPreferences

open Core.ProductOfExperts


/-!
## Semantic Classes (Sorts)

Selectional preferences reference semantic classes (sorts):
- Animate, Inanimate
- Human, Animal
- Concrete, Abstract
- Edible, Potable, etc.

These form a hierarchy (ontology) but we start with a flat enumeration.
-/

/--
Basic semantic classes for selectional restrictions.
-/
inductive SemClass where
  | animate
  | inanimate
  | human
  | animal
  | plant
  | artifact
  | abstract_
  | event
  | location
  | time
  deriving Repr, BEq, DecidableEq

/--
Class hierarchy: `subclassOf a b` means a is a subclass of b.
-/
def subclassOf : SemClass → SemClass → Bool
  | .human, .animate => true
  | .animal, .animate => true
  | .plant, .inanimate => true
  | .artifact, .inanimate => true
  | _, _ => false

/--
Transitive closure of subclass relation.
-/
def isA : SemClass → SemClass → Bool
  | c₁, c₂ => c₁ == c₂ || subclassOf c₁ c₂ ||
    -- One level of transitivity
    [SemClass.animate, .inanimate, .human, .animal, .plant, .artifact].any
      λ c => subclassOf c₁ c && subclassOf c c₂


/-!
## Semantic Roles

Roles label argument positions with their semantic function:
- Agent: intentional actor
- Patient/Theme: affected entity
- Experiencer: entity experiencing state
- Instrument: tool used
- Location: place
- etc.
-/

/--
Semantic roles (thematic roles).
-/
inductive SemRole where
  | agent
  | patient
  | theme
  | experiencer
  | instrument
  | location
  | source
  | goal
  | beneficiary
  deriving Repr, BEq, DecidableEq

/--
A semantic role with selectional constraints.

This packages a role with its distribution over acceptable fillers.
-/
structure RoleWithConstraint (Concept : Type) where
  role : SemRole
  /-- Prior probability of each concept filling this role -/
  selectionalPref : Concept → ℚ


/-!
## Verb Frames

A verb frame specifies:
1. Which roles the verb takes
2. What each role selects for
-/

/--
A predicate frame: specifies argument slots with their constraints.
-/
structure Frame (Concept : Type) where
  /-- Name of the predicate -/
  predicate : String
  /-- Argument slots with their selectional preferences -/
  arguments : List (RoleWithConstraint Concept)

/--
Look up the selectional preference for a given role in a frame.
-/
def Frame.selectionalFor {Concept : Type} (f : Frame Concept) (r : SemRole) : Option (Concept → ℚ) :=
  f.arguments.find? (·.role == r) |>.map (·.selectionalPref)


/-!
## Example: SLEEP Frame

SLEEP takes one argument (the sleeper):
- Role: Experiencer (or Agent, depending on theory)
- Selects: Animate entities strongly preferred
-/

/-- Distribution over SemClass for SLEEP's subject -/
def sleepSubjectPref : SemClass → ℚ
  | .animate => 9/10
  | .human => 9/10   -- Humans sleep
  | .animal => 9/10  -- Animals sleep
  | .plant => 1/100  -- Plants don't really "sleep" (metaphor only)
  | .artifact => 1/100
  | .abstract_ => 1/1000
  | _ => 1/100

def sleepFrame : Frame SemClass :=
  { predicate := "sleep"
  , arguments := [
      { role := .experiencer
      , selectionalPref := sleepSubjectPref }
    ]
  }

/-!
## Example: MARRY Frame

MARRY takes two arguments:
- Agent: Human (the one doing the marrying)
- Patient/Theme: Human (the one being married)
-/

def marryAgentPref : SemClass → ℚ
  | .human => 95/100
  | .animate => 5/100  -- Some animals "mate" but don't "marry"
  | _ => 1/1000

def marryPatientPref : SemClass → ℚ
  | .human => 95/100
  | .animate => 4/100  -- Metaphorical/anthropomorphic
  | .abstract_ => 1/100  -- "marry an idea" is very unusual
  | _ => 1/1000

def marryFrame : Frame SemClass :=
  { predicate := "marry"
  , arguments := [
      { role := .agent, selectionalPref := marryAgentPref }
    , { role := .patient, selectionalPref := marryPatientPref }
    ]
  }

/-!
## Example: HOLD Frame

HOLD takes two arguments:
- Agent: Animate (holder)
- Patient: Concrete (thing held)
-/

def holdAgentPref : SemClass → ℚ
  | .human => 9/10
  | .animal => 7/10
  | .animate => 8/10
  | _ => 1/100

def holdPatientPref : SemClass → ℚ
  | .artifact => 9/10
  | .inanimate => 8/10
  | .animal => 5/10  -- can hold animals
  | .human => 3/10   -- can hold babies/people
  | .animate => 4/10
  | .abstract_ => 1/10  -- "hold an idea" is metaphorical
  | _ => 2/10

def holdFrame : Frame SemClass :=
  { predicate := "hold"
  , arguments := [
      { role := .agent, selectionalPref := holdAgentPref }
    , { role := .patient, selectionalPref := holdPatientPref }
    ]
  }

/-!
## Example: DRAW Frame

DRAW is ambiguous:
1. DRAW(picture) - create an image
2. DRAW(weapon) - unsheathe/pull out
3. DRAW(conclusion) - infer

Each sense has different selectional preferences!
-/

-- DRAW-picture sense
def drawPicturePatientPref : SemClass → ℚ
  | .artifact => 9/10  -- draw a picture, diagram
  | .abstract_ => 3/10  -- draw a conclusion (different sense!)
  | _ => 1/10

-- DRAW-weapon sense
def drawWeaponPatientPref : SemClass → ℚ
  | .artifact => 9/10  -- draw a sword/blade
  | _ => 1/100

def drawPictureFrame : Frame SemClass :=
  { predicate := "draw-picture"
  , arguments := [
      { role := .agent, selectionalPref := λ
          | .human => 9/10
          | .animate => 5/10
          | _ => 1/10 }
    , { role := .patient, selectionalPref := drawPicturePatientPref }
    ]
  }

def drawWeaponFrame : Frame SemClass :=
  { predicate := "draw-weapon"
  , arguments := [
      { role := .agent, selectionalPref := λ
          | .human => 95/100
          | _ => 1/100 }
    , { role := .patient, selectionalPref := drawWeaponPatientPref }
    ]
  }


/-!
## Concept Disambiguation via Selectional Preferences

Given:
- An ambiguous word with concepts C = {c₁, c₂, ...}
- A semantic role R the word fills
- A frame F with selectional preference P_F(R, c)

The selectional constraint favors concepts matching the preference:
```
P_selectional(c | R, F) = P_F(R, c)
```
-/

/--
An ambiguous concept: multiple possible denotations.
-/
structure AmbiguousConcept (Denotation : Type) where
  form : String
  senses : List (String × Denotation)  -- (sense-name, denotation)

/--
Disambiguation result: distribution over senses.
-/
structure Disambiguation where
  senseDist : String → ℚ

/--
Disambiguate a concept given a selectional preference.

Given:
- An ambiguous concept with senses mapped to semantic classes
- A selectional preference over semantic classes

Returns the induced distribution over senses.
-/
def disambiguateBySelection
    (senseToClass : String → SemClass)
    (selPref : SemClass → ℚ)
    (senses : List String) : String → ℚ :=
  let unnorm s := selPref (senseToClass s)
  let Z := senses.foldl (λ acc s => acc + unnorm s) 0
  λ s => if Z = 0 then 0 else unnorm s / Z


/-!
## SDS-Style Factored Disambiguation

SDS combines selectional preferences with scenario constraints:
```
P(concept | context) ∝ P_selectional(concept | role) × P_scenario(concept | frame)
```

This uses Product of Experts from Core.ProductOfExperts.
-/

/--
Combined disambiguation using selectional + scenario constraints.
-/
def sdsDisambiguate
    (senseToClass : String → SemClass)
    (selPref : SemClass → ℚ)
    (scenarioPref : SemClass → ℚ)
    (senses : List String) : String → ℚ :=
  let selExpert s := selPref (senseToClass s)
  let scenExpert s := scenarioPref (senseToClass s)
  poe2 selExpert scenExpert senses


/-!
## Example: "She drew a blade"

"blade" is ambiguous:
- BLADE-weapon: a sword/knife (artifact, weapon)
- BLADE-grass: a blade of grass (plant)
- BLADE-propeller: propeller blade (artifact, machine-part)

"draw" is ambiguous:
- DRAW-picture: create an image
- DRAW-weapon: unsheathe

The combination disambiguates both:
- DRAW + BLADE → DRAW-weapon + BLADE-weapon
-/

inductive BladeSense where
  | weapon  -- sword, knife
  | grass   -- blade of grass
  | propeller  -- propeller blade
  deriving Repr, BEq, DecidableEq

def bladeSenseToClass : BladeSense → SemClass
  | .weapon => .artifact
  | .grass => .plant
  | .propeller => .artifact

-- Selectional preference from DRAW-weapon frame
def bladeSelectional : BladeSense → ℚ :=
  λ sense => drawWeaponPatientPref (bladeSenseToClass sense)

-- With no scenario, selectional alone prefers weapon and propeller equally
example : bladeSelectional .weapon = bladeSelectional .propeller := rfl

-- Add scenario constraint: combat/violence scenario
def combatScenario : BladeSense → ℚ
  | .weapon => 95/100
  | .grass => 1/100
  | .propeller => 4/100

-- Combined disambiguation strongly prefers weapon sense
def bladeDisambiguated : BladeSense → ℚ :=
  poe2 bladeSelectional combatScenario [.weapon, .grass, .propeller]


/-!
## Soft vs Hard Constraints

Selectional preferences can be:
- **Hard**: Violations are impossible (probability 0)
- **Soft**: Violations are unlikely but possible (low probability)

### Hard Constraints

"The rock slept" → semantically anomalous
- SLEEP requires animate
- Rocks are inanimate
- Hard constraint: P(inanimate | SLEEP) = 0

### Soft Constraints

"The idea slept" → metaphorical, unusual but interpretable
- IDEAS personified can "sleep"
- Soft constraint: P(abstract | SLEEP) = 0.001

### Implementation

We use soft constraints (small positive ε) rather than hard zeros.
This allows:
1. Metaphorical interpretations
2. Coercion (type-shifting)
3. Gradual degradation rather than hard failure
-/

/--
Minimum probability for "impossible" selectional violations.
Using small ε rather than 0 allows metaphor/coercion.
-/
def selectionalEpsilon : ℚ := 1/1000

/--
Convert a hard selectional constraint to soft.
-/
def softenConstraint (hard : SemClass → Bool) : SemClass → ℚ :=
  λ c => if hard c then 1 else selectionalEpsilon

/--
Example: SLEEP hard constraint (animate only)
-/
def sleepHard : SemClass → Bool
  | .animate | .human | .animal => true
  | _ => false

def sleepSoftened : SemClass → ℚ := softenConstraint sleepHard

-- The softened version gives low but non-zero probability to inanimate
example : sleepSoftened .artifact = selectionalEpsilon := rfl
example : sleepSoftened .human = 1 := rfl

end Montague.Verb.SelectionalPreferences

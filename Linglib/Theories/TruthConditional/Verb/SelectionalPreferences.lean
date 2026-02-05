/-
Selectional preferences: semantic constraints on argument slots.
Integrates with Erk & Herbelot (2024) Product of Experts for disambiguation.

- Resnik, P. (1996). Selectional constraints: An information-theoretic model.
- Erk, K. (2007). A simple, similarity-based model for selectional preferences.
- Erk, K. & Herbelot, A. (2024). How to Marry a Star. Journal of Semantics.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.Core.ProductOfExperts

namespace TruthConditional.Verb.SelectionalPreferences

open Core.ProductOfExperts


section Classes

/-- Basic semantic classes for selectional restrictions. -/
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

/-- Class hierarchy: `subclassOf a b` means a is a subclass of b. -/
def subclassOf : SemClass → SemClass → Bool
  | .human, .animate => true
  | .animal, .animate => true
  | .plant, .inanimate => true
  | .artifact, .inanimate => true
  | _, _ => false

/-- Transitive closure of subclass relation. -/
def isA : SemClass → SemClass → Bool
  | c₁, c₂ => c₁ == c₂ || subclassOf c₁ c₂ ||
    [SemClass.animate, .inanimate, .human, .animal, .plant, .artifact].any
      λ c => subclassOf c₁ c && subclassOf c c₂

end Classes

section Roles

/-- Semantic roles (thematic roles). -/
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

/-- A semantic role with its distribution over acceptable fillers. -/
structure RoleWithConstraint (Concept : Type) where
  role : SemRole
  /-- Prior probability of each concept filling this role. -/
  selectionalPref : Concept → ℚ

end Roles

section Frames

/-- A predicate frame: specifies argument slots with their constraints. -/
structure Frame (Concept : Type) where
  /-- Name of the predicate -/
  predicate : String
  /-- Argument slots with their selectional preferences -/
  arguments : List (RoleWithConstraint Concept)

/-- Look up the selectional preference for a given role in a frame. -/
def Frame.selectionalFor {Concept : Type} (f : Frame Concept) (r : SemRole) : Option (Concept → ℚ) :=
  f.arguments.find? (·.role == r) |>.map (·.selectionalPref)


/-- Distribution over SemClass for SLEEP's subject. -/
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

def marryAgentPref : SemClass → ℚ
  | .human => 95/100
  | .animate => 5/100
  | _ => 1/1000

def marryPatientPref : SemClass → ℚ
  | .human => 95/100
  | .animate => 4/100
  | .abstract_ => 1/100
  | _ => 1/1000

def marryFrame : Frame SemClass :=
  { predicate := "marry"
  , arguments := [
      { role := .agent, selectionalPref := marryAgentPref }
    , { role := .patient, selectionalPref := marryPatientPref }
    ]
  }

def holdAgentPref : SemClass → ℚ
  | .human => 9/10
  | .animal => 7/10
  | .animate => 8/10
  | _ => 1/100

def holdPatientPref : SemClass → ℚ
  | .artifact => 9/10
  | .inanimate => 8/10
  | .animal => 5/10
  | .human => 3/10
  | .animate => 4/10
  | .abstract_ => 1/10
  | _ => 2/10

def holdFrame : Frame SemClass :=
  { predicate := "hold"
  , arguments := [
      { role := .agent, selectionalPref := holdAgentPref }
    , { role := .patient, selectionalPref := holdPatientPref }
    ]
  }

def drawPicturePatientPref : SemClass → ℚ
  | .artifact => 9/10
  | .abstract_ => 3/10
  | _ => 1/10

def drawWeaponPatientPref : SemClass → ℚ
  | .artifact => 9/10
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


end Frames

section Disambiguation

/-- An ambiguous concept: multiple possible denotations. -/
structure AmbiguousConcept (Denotation : Type) where
  form : String
  senses : List (String × Denotation)  -- (sense-name, denotation)

/-- Disambiguation result: distribution over senses. -/
structure Disambiguation where
  senseDist : String → ℚ

/-- Disambiguate a concept given a selectional preference over semantic classes. -/
def disambiguateBySelection
    (senseToClass : String → SemClass)
    (selPref : SemClass → ℚ)
    (senses : List String) : String → ℚ :=
  let unnorm s := selPref (senseToClass s)
  let Z := senses.foldl (λ acc s => acc + unnorm s) 0
  λ s => if Z = 0 then 0 else unnorm s / Z


/-- Combined disambiguation using selectional + scenario constraints (SDS-style PoE). -/
def sdsDisambiguate
    (senseToClass : String → SemClass)
    (selPref : SemClass → ℚ)
    (scenarioPref : SemClass → ℚ)
    (senses : List String) : String → ℚ :=
  let selExpert s := selPref (senseToClass s)
  let scenExpert s := scenarioPref (senseToClass s)
  poe2 selExpert scenExpert senses


inductive BladeSense where
  | weapon  -- sword, knife
  | grass   -- blade of grass
  | propeller  -- propeller blade
  deriving Repr, BEq, DecidableEq

def bladeSenseToClass : BladeSense → SemClass
  | .weapon => .artifact
  | .grass => .plant
  | .propeller => .artifact

def bladeSelectional : BladeSense → ℚ :=
  λ sense => drawWeaponPatientPref (bladeSenseToClass sense)

example : bladeSelectional .weapon = bladeSelectional .propeller := rfl

def combatScenario : BladeSense → ℚ
  | .weapon => 95/100
  | .grass => 1/100
  | .propeller => 4/100

def bladeDisambiguated : BladeSense → ℚ :=
  poe2 bladeSelectional combatScenario [.weapon, .grass, .propeller]


end Disambiguation

section SoftConstraints

/-- Minimum probability for "impossible" selectional violations (allows metaphor/coercion). -/
def selectionalEpsilon : ℚ := 1/1000

/-- Convert a hard selectional constraint to soft. -/
def softenConstraint (hard : SemClass → Bool) : SemClass → ℚ :=
  λ c => if hard c then 1 else selectionalEpsilon

/-- SLEEP hard constraint (animate only). -/
def sleepHard : SemClass → Bool
  | .animate | .human | .animal => true
  | _ => false

def sleepSoftened : SemClass → ℚ := softenConstraint sleepHard

example : sleepSoftened .artifact = selectionalEpsilon := rfl
example : sleepSoftened .human = 1 := rfl

end SoftConstraints

end TruthConditional.Verb.SelectionalPreferences

/-
Selectional preferences: semantic constraints on argument slots.

- Resnik, P. (1996). Selectional constraints: An information-theoretic model.
- Erk, K. (2007). A simple, similarity-based model for selectional preferences.
- Erk, K. & Herbelot, A. (2024). How to Marry a Star. Journal of Semantics.

## Substrate

This file provides ℚ-valued selectional preferences (`Concept → ℚ`)
suitable for decidable computation in Fragment definitions. For
probabilistic disambiguation combining selectional and scenario
constraints, use mathlib's `PMF.productOfExperts`
(`Core/Probability/PMFPosterior.lean`) on PMFs constructed via
`PMF.normalize` from the score functions defined here. The newer SDS
substrate (`Theories/Semantics/Probabilistic/SDS/ConceptNode.lean`)
provides the PMF-typed `Role → PMF Concept` form for paper replications.
-/

import Mathlib.Data.Rat.Defs

namespace Semantics.Verb.SelectionalPreferences


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
  deriving Repr, DecidableEq

/-- Class hierarchy: `SubclassOf a b` means a is a subclass of b. -/
def SubclassOf : SemClass → SemClass → Prop
  | .human, .animate    => True
  | .animal, .animate   => True
  | .plant, .inanimate  => True
  | .artifact, .inanimate => True
  | _, _                => False

instance : ∀ a b, Decidable (SubclassOf a b) := fun a b => by
  cases a <;> cases b <;> unfold SubclassOf <;> infer_instance

/-- Transitive closure of subclass relation. -/
def IsA (c₁ c₂ : SemClass) : Prop :=
  c₁ = c₂ ∨ SubclassOf c₁ c₂ ∨
    ∃ c ∈ [SemClass.animate, .inanimate, .human, .animal, .plant, .artifact],
      SubclassOf c₁ c ∧ SubclassOf c c₂

instance : ∀ a b, Decidable (IsA a b) := fun a b => by
  unfold IsA; infer_instance

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
  deriving Repr, DecidableEq

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

/-! ## Disambiguation

For sense disambiguation combining selectional + scenario constraints,
use `PMF.productOfExperts` (`Core/Probability/PMFPosterior.lean`) on
PMFs constructed via `PMF.normalize` from the score functions in this
file. The illustrative ℚ-valued helpers that previously lived here
(`disambiguateBySelection`, `sdsDisambiguate`, `bladeDisambiguated`)
were removed in favor of the canonical PMF API. -/

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

end Semantics.Verb.SelectionalPreferences

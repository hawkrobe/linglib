import Linglib.Theories.Semantics.Dynamic.Systems.BSML.FreeChoice

/-!
# @cite{aloni-2022}: BSML Applied to Permission Disjunction
@cite{aloni-2022}

Phenomena-level instantiation of BSML for the classic free choice example:
"You may have coffee or tea" → "You may have coffee AND you may have tea."

The core BSML theory (formulas, support, enrichment, FC theorems) lives in
`Theories/Semantics/Dynamic/Systems/BSML/`. This file provides the concrete
deontic model and verifies the FC predictions computationally.

-/

namespace Phenomena.Modality.Studies.Aloni2022

open Semantics.Dynamic.TeamSemantics
open Semantics.Dynamic.BSML

-- ============================================================================
-- Permission World Type
-- ============================================================================

/-- Example world type for "You may have coffee or tea" -/
inductive PermissionWorld where
  | neither : PermissionWorld
  | onlyCoffee : PermissionWorld
  | onlyTea : PermissionWorld
  | both : PermissionWorld
  deriving DecidableEq, Repr

/-- The proposition "coffee is permitted" -/
def coffeePermitted : PermissionWorld → Bool
  | .onlyCoffee => true
  | .both => true
  | _ => false

/-- The proposition "tea is permitted" -/
def teaPermitted : PermissionWorld → Bool
  | .onlyTea => true
  | .both => true
  | _ => false

/-- All permission worlds -/
def permissionWorlds : List PermissionWorld :=
  [.neither, .onlyCoffee, .onlyTea, .both]

-- ============================================================================
-- Deontic Models
-- ============================================================================

/-- Deontic model: universal accessibility -/
def deonticModel : BSMLModel PermissionWorld where
  worlds := permissionWorlds
  access := λ _ => Team.full
  valuation := λ p w =>
    match p with
    | "coffee" => coffeePermitted w
    | "tea" => teaPermitted w
    | _ => false

/-- Restrictive deontic model: from 'neither', only 'neither' is accessible -/
def restrictiveModel : BSMLModel PermissionWorld where
  worlds := permissionWorlds
  access := λ w =>
    match w with
    | .neither => λ w' => w' == .neither
    | _ => Team.full
  valuation := λ p w =>
    match p with
    | "coffee" => coffeePermitted w
    | "tea" => teaPermitted w
    | _ => false

-- ============================================================================
-- Formulas
-- ============================================================================

/-- The formula ◇(coffee ∨ tea) -/
def mayHaveCoffeeOrTea : BSMLFormula :=
  .poss (.disj (.atom "coffee") (.atom "tea"))

/-- Team representing "free choice holds" (both options available) -/
def freeChoiceTeam : Team PermissionWorld :=
  λ w => w == .both || w == .onlyCoffee || w == .onlyTea

def mayCoffee : BSMLFormula := .poss (.atom "coffee")
def mayTea : BSMLFormula := .poss (.atom "tea")

def prohibition : BSMLFormula :=
  .neg (.poss (.disj (.atom "coffee") (.atom "tea")))

def notMayCoffee : BSMLFormula := .neg (.poss (.atom "coffee"))
def notMayTea : BSMLFormula := .neg (.poss (.atom "tea"))

/-- Team where neither is permitted (with restricted accessibility) -/
def prohibitionTeam : Team PermissionWorld :=
  λ w => w == .neither

def wideScopeDisj : BSMLFormula :=
  .disj (.poss (.atom "coffee")) (.poss (.atom "tea"))

-- ============================================================================
-- Computational Verification
-- ============================================================================

#guard support deonticModel (enrich mayHaveCoffeeOrTea) freeChoiceTeam
#guard support deonticModel mayCoffee freeChoiceTeam
#guard support deonticModel mayTea freeChoiceTeam
#guard support restrictiveModel (enrich prohibition) prohibitionTeam
#guard support restrictiveModel notMayCoffee prohibitionTeam
#guard support restrictiveModel notMayTea prohibitionTeam
#guard support deonticModel (enrich wideScopeDisj) freeChoiceTeam
#guard deonticModel.isIndisputable freeChoiceTeam

end Phenomena.Modality.Studies.Aloni2022

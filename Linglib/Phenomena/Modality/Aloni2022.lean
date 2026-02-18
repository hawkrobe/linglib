import Linglib.Theories.Semantics.Dynamic.Systems.BSML.FreeChoice

/-!
# Aloni (2022): BSML Applied to Permission Disjunction

Phenomena-level instantiation of BSML for the classic free choice example:
"You may have coffee or tea" → "You may have coffee AND you may have tea."

The core BSML theory (formulas, support, enrichment, FC theorems) lives in
`Theories/Semantics/Dynamic/Systems/BSML/`. This file provides the concrete
deontic model and verifies the FC predictions computationally.

## References

- Aloni, M. (2022). Logic and conversation: The case of free choice. S&P 15.
  @cite{aloni-2022}
-/

namespace Phenomena.Modality.Aloni2022

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

-- Verify: the enriched formula supports free choice inference
#eval support deonticModel (enrich mayHaveCoffeeOrTea) freeChoiceTeam

-- The free choice consequences
#eval support deonticModel mayCoffee freeChoiceTeam
#eval support deonticModel mayTea freeChoiceTeam

-- Verify NARROW-SCOPE FC
#eval
  let enriched := enrich mayHaveCoffeeOrTea
  let supEnriched := support deonticModel enriched freeChoiceTeam
  let supCoffee := support deonticModel mayCoffee freeChoiceTeam
  let supTea := support deonticModel mayTea freeChoiceTeam
  (supEnriched, supCoffee, supTea)  -- Expect: (true, true, true)

-- Verify DUAL PROHIBITION
#eval
  let enrichedProhib := enrich prohibition
  let supProhib := support restrictiveModel enrichedProhib prohibitionTeam
  let supNotCoffee := support restrictiveModel notMayCoffee prohibitionTeam
  let supNotTea := support restrictiveModel notMayTea prohibitionTeam
  (supProhib, supNotCoffee, supNotTea)  -- Expect: (true, true, true)

-- Verify WIDE-SCOPE FC
#eval
  let enrichedWide := enrich wideScopeDisj
  let supWide := support deonticModel enrichedWide freeChoiceTeam
  let supCoffee := support deonticModel mayCoffee freeChoiceTeam
  let supTea := support deonticModel mayTea freeChoiceTeam
  (supWide, supCoffee, supTea)  -- Expect: (true, true, true)

-- Verify indisputability
#eval deonticModel.isIndisputable freeChoiceTeam  -- Expect: true

end Phenomena.Modality.Aloni2022

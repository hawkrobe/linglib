import Linglib.Theories.Semantics.BSML.FreeChoice

/-!
# @cite{aloni-2022}: BSML Applied to Permission Disjunction
@cite{aloni-2022}

Phenomena-level instantiation of BSML for the classic free choice example:
"You may have coffee or tea" → "You may have coffee AND you may have tea."

The core BSML theory (formulas, support, enrichment, FC theorems) lives in
`Theories/Semantics/BSML/`. This file provides the concrete
deontic model and verifies the FC predictions computationally.

-/

namespace Aloni2022

open Semantics.BSML

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

instance : Fintype PermissionWorld where
  elems := {.neither, .onlyCoffee, .onlyTea, .both}
  complete := by intro x; cases x <;> simp

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

-- ============================================================================
-- Deontic Models
-- ============================================================================

/-- Deontic model: universal accessibility -/
def deonticModel : BSMLModel PermissionWorld where
  access := λ _ => Finset.univ
  val := λ p w =>
    match p with
    | "coffee" => coffeePermitted w
    | "tea" => teaPermitted w
    | _ => false

/-- Restrictive deontic model: from 'neither', only 'neither' is accessible -/
def restrictiveModel : BSMLModel PermissionWorld where
  access := λ w =>
    match w with
    | .neither => {.neither}
    | _ => Finset.univ
  val := λ p w =>
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
def freeChoiceTeam : Finset PermissionWorld :=
  {.both, .onlyCoffee, .onlyTea}

def mayCoffee : BSMLFormula := .poss (.atom "coffee")
def mayTea : BSMLFormula := .poss (.atom "tea")

def prohibition : BSMLFormula :=
  .neg (.poss (.disj (.atom "coffee") (.atom "tea")))

def notMayCoffee : BSMLFormula := .neg (.poss (.atom "coffee"))
def notMayTea : BSMLFormula := .neg (.poss (.atom "tea"))

/-- Team where neither is permitted (with restricted accessibility) -/
def prohibitionTeam : Finset PermissionWorld :=
  {.neither}

def wideScopeDisj : BSMLFormula :=
  .disj (.poss (.atom "coffee")) (.poss (.atom "tea"))

/-- Double negation FC: ¬¬◇(coffee ∨ tea) (Fact 12) -/
def doubleNegMayHaveCoffeeOrTea : BSMLFormula :=
  .neg (.neg (.poss (.disj (.atom "coffee") (.atom "tea"))))

-- ============================================================================
-- Computational Verification
-- ============================================================================

#guard decide (support deonticModel (enrich mayHaveCoffeeOrTea) freeChoiceTeam)
#guard decide (support deonticModel mayCoffee freeChoiceTeam)
#guard decide (support deonticModel mayTea freeChoiceTeam)
#guard decide (support restrictiveModel (enrich prohibition) prohibitionTeam)
#guard decide (support restrictiveModel notMayCoffee prohibitionTeam)
#guard decide (support restrictiveModel notMayTea prohibitionTeam)
#guard decide (support deonticModel (enrich wideScopeDisj) freeChoiceTeam)
#guard decide (support deonticModel (enrich doubleNegMayHaveCoffeeOrTea) freeChoiceTeam)
#guard decide (support deonticModel mayCoffee freeChoiceTeam)  -- Fact 12: FC re-emerges under ¬¬
#guard decide (support deonticModel mayTea freeChoiceTeam)
#guard decide (deonticModel.isIndisputable freeChoiceTeam)

-- ============================================================================
-- Modal Disjunction (Fact 3): plain disjunction + state-based R → FC
-- ============================================================================

/-- State-based deontic model: R[w] = team for all w in team.
    This is strictly stronger than indisputability. -/
def stateBasedModel : BSMLModel PermissionWorld where
  access := λ _ => freeChoiceTeam
  val := λ p w =>
    match p with
    | "coffee" => coffeePermitted w
    | "tea" => teaPermitted w
    | _ => false

#guard decide (stateBasedModel.isStateBased freeChoiceTeam)

-- Enriched plain disjunction (no ◇) supported on state-based team
#guard decide (support stateBasedModel
  (enrich (.disj (.atom "coffee") (.atom "tea"))) freeChoiceTeam)

-- Fact 3 prediction: ◇coffee ∧ ◇tea follows from enriched plain disjunction
-- under state-based R
#guard decide (support stateBasedModel (BSMLFormula.poss (.atom "coffee")) freeChoiceTeam)
#guard decide (support stateBasedModel (BSMLFormula.poss (.atom "tea")) freeChoiceTeam)

end Aloni2022

import Linglib.Features.Prominence
import Linglib.Features.Case.Basic
import Linglib.Syntax.Agreement.Paradigm
/-!
# Basque Agreement Fragment [just-2024]
[laka-1996] [preminger-2014] [blake-1994]

Basque (isolate) has a rich agreement system where the finite verb indexes
up to three arguments: ergative (A), absolutive (S/P), and dative (R).
Crucially, object (P/R) agreement is **person-conditioned**: the verb
cross-references 1st/2nd person objects but not 3rd person objects in many
constructions.

This is a classic case of **differential P indexing** conditioned by
person prominence: SAP objects are indexed, 3rd
person objects are not.

## Agreement Paradigm Overview

| Argument | Case | Indexed? |
|----------|------|----------|
| A (transitive agent) | ERG | Always |
| S (intransitive subj) | ABS | Always |
| P (transitive patient) | ABS | SAP only (differential) |

-/

namespace Basque.Agreement

open Features.Prominence
open _root_.Agreement

-- ============================================================================
-- § 1: Argument Positions
-- ============================================================================

/-- Argument positions in a Basque clause. -/
inductive ArgPosition where
  /-- A: transitive agent (ERG) -/
  | agent
  /-- P: transitive patient (ABS) -/
  | patient
  /-- S: intransitive subject (ABS) -/
  | intranS
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Differential P Indexing
-- ============================================================================

/-- Whether a P argument at a given φ-cell is indexed on the verb. Basque
    cross-references SAP objects (1st/2nd person) but not 3rd person objects in
    the relevant constructions; A/S arguments are always indexed. Keyed by the
    canonical φ-cell (`Agreement.Cell`), so a pronoun's `Word.agrCell`
    drives it directly. -/
def pIsIndexed (c : Cell) : Bool := c.isSAP

/-- Whether an A/S argument is indexed. Always true — A and S indexing is not
    differential in Basque. -/
def asIsIndexed (_ : Cell) : Bool := true

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- SAP objects are indexed. -/
theorem sap_objects_indexed :
    pIsIndexed (.pn .first .Sing) = true ∧ pIsIndexed (.pn .second .Sing) = true ∧
    pIsIndexed (.pn .first .Plur) = true ∧ pIsIndexed (.pn .second .Plur) = true := by decide

/-- 3rd person objects are NOT indexed. -/
theorem third_objects_not_indexed :
    pIsIndexed (.pn .third .Sing) = false ∧ pIsIndexed (.pn .third .Plur) = false := by decide

/-- P indexing is differential: some φ-cells indexed, some not. -/
theorem p_indexing_differential :
    Cell.pnCells.any pIsIndexed = true ∧
    !(Cell.pnCells.all pIsIndexed) = true := by decide

/-- A/S indexing is NOT differential: all φ-cells indexed. -/
theorem as_indexing_uniform :
    Cell.pnCells.all asIsIndexed = true := by decide

-- ============================================================================
-- § 5: Case Inventory Validation ([blake-1994])
-- ============================================================================

/-- Basque agreement-relevant case inventory: {ERG, ABS, DAT}.
    The full Basque case system has ~12 cases (ERG, ABS, DAT, GEN, LOC,
    ABL, ALL, INST, COM, PERL, BEN, and more), but the agreement system
    only distinguishes these three. -/
def agreementCaseInventory : Finset Case := {.erg, .abs, .dat}

/-- The full Basque case inventory (representative selection). -/
def fullCaseInventory : Finset Case :=
  {.erg, .abs, .gen, .dat, .loc, .abl, .all, .inst, .com, .perl, .ben}

-- The full inventory is valid per Blake's hierarchy (ranks 6 down to 1,
-- all represented).
example : Case.IsValidInventory fullCaseInventory := by decide

end Basque.Agreement

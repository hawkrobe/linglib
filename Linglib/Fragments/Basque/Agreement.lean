import Linglib.Core.Prominence
import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Basque Agreement Fragment @cite{just-2024}
@cite{laka-1996} @cite{preminger-2014} @cite{blake-1994}

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

namespace Fragments.Basque.Agreement

open Core.Prominence

-- ============================================================================
-- § 1: Person-Number Values
-- ============================================================================

/-- Person-number combinations in the Basque agreement paradigm. -/
inductive PersonNumber where
  | p1sg | p2sg | p3sg | p1pl | p2pl | p3pl
  deriving DecidableEq, Repr

/-- All person-number values. -/
def allPersonNumbers : List PersonNumber :=
  [.p1sg, .p2sg, .p3sg, .p1pl, .p2pl, .p3pl]

/-- Person value (1, 2, or 3). -/
def PersonNumber.person : PersonNumber → Nat
  | .p1sg | .p1pl => 1
  | .p2sg | .p2pl => 2
  | .p3sg | .p3pl => 3

/-- Is this a SAP (speech act participant)? -/
def PersonNumber.isSAP (pn : PersonNumber) : Bool :=
  pn.person == 1 || pn.person == 2

-- ============================================================================
-- § 2: Argument Positions
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
-- § 3: Differential P Indexing
-- ============================================================================

/-- Whether a P argument at a given person-number is indexed on the verb.

    Basque cross-references SAP objects (1st/2nd person) but not 3rd
    person objects in the relevant constructions.
    A and S arguments are always indexed regardless of person. -/
def pIsIndexed (pn : PersonNumber) : Bool := pn.isSAP

/-- Whether an A/S argument at a given person-number is indexed.
    Always true — A and S indexing is not differential in Basque. -/
def asIsIndexed (_ : PersonNumber) : Bool := true

-- ============================================================================
-- § 4: Verification
-- ============================================================================

/-- SAP objects are indexed. -/
theorem sap_objects_indexed :
    pIsIndexed .p1sg = true ∧ pIsIndexed .p2sg = true ∧
    pIsIndexed .p1pl = true ∧ pIsIndexed .p2pl = true := ⟨rfl, rfl, rfl, rfl⟩

/-- 3rd person objects are NOT indexed. -/
theorem third_objects_not_indexed :
    pIsIndexed .p3sg = false ∧ pIsIndexed .p3pl = false := ⟨rfl, rfl⟩

/-- P indexing is differential: some person-numbers indexed, some not. -/
theorem p_indexing_differential :
    allPersonNumbers.any pIsIndexed = true ∧
    !(allPersonNumbers.all pIsIndexed) = true := ⟨by native_decide, by native_decide⟩

/-- A/S indexing is NOT differential: all person-numbers indexed. -/
theorem as_indexing_uniform :
    allPersonNumbers.all asIsIndexed = true := by native_decide

-- ============================================================================
-- § 5: Case Inventory Validation (@cite{blake-1994})
-- ============================================================================

/-- Basque agreement-relevant case inventory: {ERG, ABS, DAT}.
    The full Basque case system has ~12 cases (ERG, ABS, DAT, GEN, LOC,
    ABL, ALL, INST, COM, PERL, BEN, and more), but the agreement system
    only distinguishes these three. -/
def agreementCaseInventory : Finset Core.Case := {.erg, .abs, .dat}

/-- The full Basque case inventory (representative selection). -/
def fullCaseInventory : Finset Core.Case :=
  {.erg, .abs, .gen, .dat, .loc, .abl, .all, .inst, .com, .perl, .ben}

-- The full inventory is valid per Blake's hierarchy (ranks 6 down to 1,
-- all represented).
example : Core.Case.IsValidInventory fullCaseInventory := by decide

end Fragments.Basque.Agreement

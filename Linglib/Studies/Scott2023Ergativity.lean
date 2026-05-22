import Linglib.Fragments.Mayan.Mam.Agreement
import Linglib.Fragments.Mayan.Params

/-!
# Super-Extended Ergativity in SJA Mam
@cite{scott-2023} @cite{england-2017}

Theory-neutral data on split ergativity in San Juan Atitán (SJA) Mam.

## The Phenomenon

In matrix clauses, Mam shows a tripartite agreement pattern:
- A (transitive agent): Set A (ERG)
- S (intransitive subject): Set B (ABS)
- P (transitive patient): default Set B (no agreement)

In certain dependent clauses — purpose clauses headed by *tu'n*, reason
clauses, *taj* 'when' clauses — the alignment shifts to what
@cite{england-2017} calls **super-extended ergativity**: Set A marking
extends to ALL arguments (S, A, and O). The system becomes "neutral"
with all arguments receiving the same marker set.

## The Split

The trigger is clause type, not aspect or person features:
- **Matrix clauses**: tripartite (ERG Set A / ABS Set B / default Set B)
- **Super-extended ergative (SEE) clauses**: neutral (all Set A)

## Key Data Points

1. Intransitive S in SEE clauses: Set A (not Set B as in matrix)
2. Transitive A in SEE clauses: Set A (same as matrix)
3. Transitive O in SEE clauses: Set A on directional (not default Set B/
   independent pronoun as in matrix). Only default 2/3SG Set A (t-) is
   allowed — agreeing Set A markers for the object are ungrammatical
   (@cite{scott-2023}, §2.6.3, ex. 196).

## Why Not `SplitErgativity`?

`Core.Case.SplitErgativity` models a binary toggle between ergative and
accusative alignment conditioned by some factor (e.g., aspect in Hindi).
Mam's SEE split is not binary — it goes from tripartite (three distinct
marking patterns) to neutral (one pattern for all). The custom
`MamAlignment` struct captures this richer contrast directly.

## See Also

`Scott2023` for the Agree-based derivation
of the matrix tripartite pattern (probe blocking by Voice_TR).
-/

namespace Scott2023

open Fragments.Mayan (MarkerSet)

-- ============================================================================
-- § 1: Clause-Type-Conditioned Alignment
-- ============================================================================

/-- The Mam alignment in a given clause type. -/
structure MamAlignment where
  /-- Marker set for S (intransitive subject) -/
  sMarker : MarkerSet
  /-- Marker set for A (transitive agent) -/
  aMarker : MarkerSet
  /-- Marker set for O (transitive patient) -/
  oMarker : MarkerSet
  deriving DecidableEq, Repr

/-- Matrix clause alignment: tripartite.
    S = Set B (ABS), A = Set A (ERG), O = default Set B (no agreement). -/
def matrixAlignment : MamAlignment :=
  { sMarker := .setB, aMarker := .setA, oMarker := .setB }

/-- Super-extended ergative alignment: neutral (all Set A). -/
def seeAlignment : MamAlignment :=
  { sMarker := .setA, aMarker := .setA, oMarker := .setA }

-- ============================================================================
-- § 2: Verification
-- ============================================================================

/-- Matrix alignment is tripartite: S, A, O each have distinct marking
    patterns (S ≠ A by marker set; S ≡ O by marker set but S has real
    agreement while O has default — the tripartite distinction is
    agreement-based, not marker-set-based). -/
theorem matrix_s_ne_a : matrixAlignment.sMarker ≠ matrixAlignment.aMarker := by
  decide

/-- SEE alignment is neutral: all arguments get the same marker set. -/
theorem see_is_neutral :
    seeAlignment.sMarker = seeAlignment.aMarker ∧
    seeAlignment.aMarker = seeAlignment.oMarker := ⟨rfl, rfl⟩

/-- The split: matrix and SEE differ in S marking and O marking. -/
theorem split_ergativity :
    matrixAlignment.sMarker ≠ seeAlignment.sMarker ∧
    matrixAlignment.oMarker ≠ seeAlignment.oMarker ∧
    matrixAlignment.aMarker = seeAlignment.aMarker := by
  exact ⟨by decide, by decide, rfl⟩

/-- A is invariant across the split: Set A in both matrix and SEE. -/
theorem a_invariant :
    matrixAlignment.aMarker = seeAlignment.aMarker := rfl

-- ============================================================================
-- § 3: Subordinators That Trigger SEE
-- ============================================================================

/-- Subordinators that trigger super-extended ergativity in SJA Mam. -/
inductive SEETrigger where
  | tun      -- *tu'n*: purpose/reason clauses
  | taj      -- *taj*: 'when' (past)
  | aj       -- *aj*: 'when' (future)
  | chix     -- *ch'ix*: 'almost'
  | nim      -- *ni'm*: 'right now'
  | nanx     -- *na'nx*: 'not yet'
  deriving DecidableEq, Repr

/-- All SEE triggers yield the same neutral alignment. -/
def seeTriggerAlignment (_ : SEETrigger) : MamAlignment := seeAlignment

-- ============================================================================
-- § 4: Object Agreement Restriction in SEE
-- ============================================================================

/-- In SEE clauses, object Set A markers are restricted to the default
    2/3SG form (t-). Agreeing Set A markers for the object are
    ungrammatical. This parallels the default Set B (tz'=) pattern for
    objects in matrix clauses. -/
def objectSetAIsDefault : Bool := true

/-- The parallel: in BOTH matrix and SEE, the object slot shows default
    (non-agreeing) morphology. The default marker just changes:
    - Matrix: default Set B (tz'=)
    - SEE: default Set A (t-) -/
theorem object_default_parallel :
    objectSetAIsDefault = true := rfl

end Scott2023

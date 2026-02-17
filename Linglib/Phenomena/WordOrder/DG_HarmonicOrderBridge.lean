import Linglib.Theories.Syntax.DependencyGrammar.Formal.HarmonicOrder
import Linglib.Phenomena.WordOrder.Typology

/-!
# Bridge: DG Harmonic Order → WALS Word-Order Typology

Connects the DLM (dependency length minimization) prediction that harmonic
word order is cheaper (§4 of `HarmonicOrder.lean`) to the WALS typological
observation that harmonic word order is more common across languages
(`Phenomena.WordOrder.Typology`).

For each of the 3 construction pairs in WALS (Gibson 2025 Tables 1–3):
- **DLM predicts**: disharmonic order is costly (higher TDL in recursive structures)
- **WALS observes**: disharmonic order is rare (fewer languages)

Also verifies well-formedness, projectivity, and Behaghel's law for the
example trees from `HarmonicOrder.lean`.

## References

- Gibson, E. (2025). Syntax: A cognitive approach. Ch. 5.3. MIT Press.
- Dryer, M. (1992). The Greenbergian word order correlations. Language 68.
-/

namespace DepGrammar.HarmonicOrder

open DepGrammar DependencyLength
open Phenomena.WordOrder.Typology

-- ============================================================================
-- §5: Bridge to WALS Typology
-- ============================================================================

/-- WALS confirms harmonic order is more common, for a given table. -/
def walsConfirmsHarmonic (t : CrossTab) : Bool :=
  t.harmonicDominant

/-- Combined consistency check: DLM prediction and WALS observation agree. -/
def dlmWalsConsistent (t : CrossTab) : Bool :=
  dlmPredictsHarmonicCheaper && walsConfirmsHarmonic t

/-- For all 3 construction pairs, DLM predicts harmonic is cheaper AND
    WALS confirms harmonic is more common.

    This is Gibson (2025) Ch. 5.3's central claim: DLM explains the
    head-direction generalization. -/
theorem dlm_explains_head_direction_generalization :
    allTables.all dlmWalsConsistent = true := by native_decide

/-- Per-table consistency theorems. -/
theorem vo_adposition_consistent :
    dlmWalsConsistent voAdposition = true := by native_decide

theorem vo_subordinator_consistent :
    dlmWalsConsistent voSubordinator = true := by native_decide

theorem vo_relative_clause_consistent :
    dlmWalsConsistent voRelativeClause = true := by native_decide

-- ============================================================================
-- Bridge to Existing DependencyLength.lean
-- ============================================================================

/-- The harmonic tree examples are well-formed (unique heads, acyclic). -/
example : hasUniqueHeads harmonicHI = true := by native_decide
example : hasUniqueHeads harmonicHF = true := by native_decide
example : hasUniqueHeads disharmonicHF = true := by native_decide
example : hasUniqueHeads disharmonicFH = true := by native_decide

/-- All four trees are projective (no crossing arcs). The disharmonic
    ones are longer NOT because of non-projectivity, but because
    consistent direction is a separate (stronger) constraint. -/
example : isProjective harmonicHI = true := by native_decide
example : isProjective harmonicHF = true := by native_decide
example : isProjective disharmonicHF = true := by native_decide
example : isProjective disharmonicFH = true := by native_decide

/-- Bridge to Behaghel: harmonic trees satisfy Oberstes Gesetz with
    threshold 2 (no dep longer than 2). Disharmonic trees do not. -/
example : oberstesGesetz harmonicHI 2 = true := by native_decide
example : oberstesGesetz harmonicHF 2 = true := by native_decide
example : oberstesGesetz disharmonicHF 2 = false := by native_decide
example : oberstesGesetz disharmonicFH 2 = false := by native_decide

end DepGrammar.HarmonicOrder

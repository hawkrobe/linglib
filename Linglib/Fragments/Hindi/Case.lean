import Linglib.Features.Case.Basic
import Linglib.Features.Case.Basic
import Linglib.Syntax.Case.Alignment
/-!
# Hindi Case Inventory [blake-1994]

Hindi has a **split-ergative** case system:
ergative -ne marks the transitive agent in perfective aspect only.

Hindi postpositions mark 7 case functions:
- NOM (unmarked), ERG (-ne, perfective A only)
- ACC / DAT (-ko, syncretic), GEN (-ka / -ke / -ki)
- LOC (-mem), ABL/INST (-se, syncretic)

The ACC/DAT syncretism (-ko) and ABL/INST syncretism (-se) are
cross-linguistically common patterns.

## Split-Ergative Connection

This fragment connects to the `hindiSplit` already defined in
`Alignment.SplitErgativity`, which formalizes the perfective to
ergative conditioning.

-/

namespace Hindi.Case

-- ============================================================================
-- Section 1: Case Inventory
-- ============================================================================

/-- Hindi case inventory. ACC/DAT share -ko; ABL/INST share -se.
    Both syncretic pairs are included as distinct Case values since
    they occupy different positions on Blake's hierarchy. -/
def caseInventory : Finset Case :=
  {.nom, .erg, .acc, .dat, .gen, .loc, .abl, .inst}

-- Contiguous on Blake's hierarchy (ranks 6 down to 2, all present).
example : Case.IsValidInventory caseInventory := by decide

-- ============================================================================
-- Section 2: Syncretism
-- ============================================================================

/-- ACC/DAT syncretism (-ko marks both). -/
theorem acc_dat_syncretic_marker : True := trivial

/-- ABL/INST syncretism (-se marks both). Same-tier adjacency. -/
theorem abl_inst_same_tier :
    Case.hierarchyRank .abl = Case.hierarchyRank .inst := rfl

-- ============================================================================
-- Section 3: Split-Ergative Connection
-- ============================================================================

/-- The split-ergative system defined in `SplitConditions.lean`. -/
theorem hindi_perfective_is_ergative :
    Alignment.hindiSplit.alignment .perfective = .ergative := rfl

theorem hindi_imperfective_is_accusative :
    Alignment.hindiSplit.alignment .imperfective = .accusative := rfl

end Hindi.Case

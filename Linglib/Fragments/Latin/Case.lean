import Linglib.Features.Case.Basic
import Linglib.Features.Case.Basic
import Linglib.Features.Case.Grammaticalization

/-!
# Latin Case Inventory [blake-1994]

Latin has **6 cases** in the standard description ([blake-1994], passim):
NOM, ACC, GEN, DAT, ABL, VOC. Latin is Blake's primary example language
throughout *Case* — its paradigms illustrate syncretism patterns (Ch. 2,
pp. 19–24), the core/peripheral distinction, and the ABL's wide functional
range (source, instrument, cause, comparison).

A vestigial **locative** survives for a few nouns (place names, *domī*
'at home', *humī* 'on the ground'). Including it gives a 7-case inventory
that satisfies Blake's contiguity; the standard 6-case inventory has a gap
at rank 3 (LOC) between DAT and ABL.

## Syncretism

Latin syncretism patterns divide into two groups:
- NOM + ACC: neuter nouns (2nd, 3rd, 4th declension)
- DAT + ABL: plural across all declensions

-/

namespace Latin.Case

-- ============================================================================
-- § 1: Case Inventory
-- ============================================================================

/-- Standard Latin 6-case inventory (NOM ACC GEN DAT ABL VOC). -/
def caseInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .abl, .voc}

/-- The hierarchy-relevant subset (excluding VOC at rank 0). -/
def coreInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .abl}

/-- Latin's 5-case core inventory **fails** strict contiguity: DAT (rank 4)
    and ABL (rank 2) have no LOC (rank 3) between them. -/
theorem core_inventory_fails_strict :
    ¬ Case.IsValidInventory coreInventory := by decide

/-- With the vestigial locative, contiguous on ranks 6–2.
    VOC (rank 0) creates a gap at rank 1 under strict checking, so
    we validate the hierarchy-relevant subset without it. -/
def inventoryWithLocative : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .abl}

example : Case.IsValidInventory inventoryWithLocative := by decide

-- ============================================================================
-- § 2: Syncretism Patterns ([blake-1994], pp. 19–24)
-- ============================================================================

theorem neuter_syncretism_adjacent :
    Case.HierarchyAdjacent .nom .acc := by decide

theorem dat_abl_not_strictly_adjacent :
    ¬ Case.HierarchyAdjacent .dat .abl := by decide

theorem dat_abl_inventory_adjacent :
    Case.InventoryAdjacent coreInventory .dat .abl := by decide

-- ============================================================================
-- § 3: Case Extension ([heine-2009], Table 29.6)
-- ============================================================================

/-- Latin ABL is the textbook case of case extension: a single
    morphological form covers source (ablativus separativus), instrumental
    (ablativus instrumenti), and causal (ablativus causae) functions.
    These are exactly the ablative extension targets in [heine-2009]
    Table 29.6, formalized in `Case.Extends`. -/
theorem abl_extends_to_inst :
    Case.Extends .abl .inst := by decide

theorem abl_extends_to_caus :
    Case.Extends .abl .caus := by decide

end Latin.Case

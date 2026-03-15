import Linglib.Core.Case
import Linglib.Theories.Morphology.CaseContainment
open Theories.Morphology.CaseContainment

/-!
# Latin Case Inventory @cite{blake-1994}

Latin has **6 cases** in the standard description (@cite{blake-1994}, passim):
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

namespace Fragments.Latin.Case

-- ============================================================================
-- § 1: Case Inventory
-- ============================================================================

/-- Standard Latin 6-case inventory (NOM ACC GEN DAT ABL VOC). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .abl, .voc]

/-- The hierarchy-relevant subset (excluding VOC at rank 0). -/
def coreInventory : List Core.Case :=
  [.nom, .acc, .gen, .dat, .abl]

/-- Latin's 5-case core inventory **fails** strict contiguity: DAT (rank 4)
    and ABL (rank 2) have no LOC (rank 3) between them. -/
theorem core_inventory_fails_strict :
    Core.validInventory coreInventory = false := by native_decide

/-- With the vestigial locative, contiguous on ranks 6–2.
    VOC (rank 0) creates a gap at rank 1 under strict checking, so
    we validate the hierarchy-relevant subset without it. -/
def inventoryWithLocative : List Core.Case :=
  [.nom, .acc, .gen, .dat, .loc, .abl]

theorem inventory_with_loc_valid :
    Core.validInventory inventoryWithLocative = true := by native_decide

-- ============================================================================
-- § 2: Syncretism Patterns (@cite{blake-1994}, pp. 19–24)
-- ============================================================================

/-- NOM/ACC syncretism in neuter nouns (2nd, 3rd, 4th declension).
    Instantiates the cross-linguistic NOM/ACC pattern from `Core.Case.Syncretism`. -/
def neuterSyncretism : Syncretism := nomAccSyncretism

/-- NOM/ACC is same-tier (both rank 6) — trivially adjacent. -/
theorem neuter_syncretism_adjacent :
    hierarchyAdjacent .nom .acc = true := by native_decide

/-- DAT/ABL syncretism in the plural. -/
def pluralDatAblSyncretism : Syncretism :=
  ⟨.dat, .abl, by decide⟩

/-- DAT/ABL are NOT strictly adjacent on the hierarchy (ranks 4, 2) —
    LOC (rank 3) intervenes. But they ARE inventory-adjacent in the
    standard 6-case system that lacks LOC. -/
theorem dat_abl_not_strictly_adjacent :
    hierarchyAdjacent .dat .abl = false := by native_decide

theorem dat_abl_inventory_adjacent :
    inventoryAdjacent coreInventory .dat .abl = true := by native_decide

-- ============================================================================
-- § 3: Local Case Extension (@cite{blake-1994}, Ch. 6)
-- ============================================================================

/-- Latin ABL is the textbook case of local case extension: a single
    morphological form covers source (ablativus separativus), instrumental
    (ablativus instrumenti), and causal (ablativus causae) functions.
    This is exactly the ABL → INST → CAUS grammaticalization path
    formalized in `Core.Case.LocalExtension`. -/
theorem abl_extends_to_inst :
    Core.Case.inst ∈ Core.localExtension .abl := by simp [Core.localExtension]

theorem abl_extends_to_caus :
    Core.Case.caus ∈ Core.localExtension .abl := by simp [Core.localExtension]

end Fragments.Latin.Case

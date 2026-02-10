import Linglib.Theories.IntensionalSemantics.Modal.Typology
import Linglib.Fragments.English.FunctionWords

/-!
# Cross-Linguistic Modal Typology

Empirical modal inventories from 27 languages (17 families) mapped to the
2×3 force-flavor meaning space, following Imel, Guo, & Steinert-Threlkeld (2026).

## Mapping conventions (raw typological data → 2×3 grid)

* Force: weak → `.possibility`, strong → `.necessity`, weak necessity → `.necessity`
* Flavor: epistemic → `.epistemic`, deontic → `.deontic`,
  circumstantial → `.circumstantial`, teleological → `.circumstantial`
* Bouletic, reportative, ability, intentional flavors are outside the 2×3 space
  and are dropped from the mapping.
* Only positive-polarity, `can_express = 1` entries are included.

## Data source

Guo, Imel, & Steinert-Threlkeld (2022). A database for modal semantic typology.
https://clmbr.shane.st/modal-typology/

## References

* Imel, N., Guo, Q., & Steinert-Threlkeld, S. (2026). An Efficient Communication
  Analysis of Modal Typology. Open Mind 10, 1–28.
-/

namespace Phenomena.Modality.Typology

open Core.ModalLogic (ModalForce ModalFlavor ForceFlavor)
open IntensionalSemantics.Modal.Typology (ModalExpression ModalInventory satisfiesIFF)

/-! ## Abbreviations for the six meaning points -/

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

-- ============================================================================
-- §1: Tlingit (Athabaskan-Eyak-Tlingit) — Cable (2017)
-- ============================================================================

def tlingit : ModalInventory where
  language := "Tlingit"
  family := "Athabaskan-Eyak-Tlingit"
  source := "Cable (2017)"
  expressions := [
    ⟨"gwal",           [pe]⟩,
    ⟨"giwe",           [pe]⟩,
    ⟨"shákdé",         [pe]⟩,
    ⟨"future mode",    [nc]⟩,
    ⟨"potential mode",  [pc]⟩
  ]

theorem tlingit_all_iff : tlingit.allIFF = true := by native_decide
theorem tlingit_size : tlingit.size = 5 := by native_decide
theorem tlingit_has_synonymy : tlingit.hasSynonymy = true := by native_decide

-- ============================================================================
-- §2: Javanese-Paciran (Austronesian) — Vander Klok (2013a)
-- ============================================================================

def javanese : ModalInventory where
  language := "Javanese"
  family := "Austronesian"
  source := "Vander Klok (2013a)"
  expressions := [
    ⟨"mesthi",    [ne]⟩,
    ⟨"mesthi-ne", [ne]⟩,
    ⟨"paleng",    [pe]⟩,
    ⟨"oleh",      [pd]⟩,
    ⟨"iso",       [pc]⟩,
    ⟨"kudu1",     [nd, nc]⟩,
    ⟨"kudu1-ne",  [nd, nc]⟩
  ]

theorem javanese_all_iff : javanese.allIFF = true := by native_decide
theorem javanese_size : javanese.size = 7 := by native_decide

-- ============================================================================
-- §3: Gitksan (Tsimshian) — Matthewson (2013)
-- ============================================================================

/-- Gitksan has variable-force modals: ima('a) and gat express both
    weak and strong epistemic force. These satisfy SAV (varying on force only,
    single flavor) and IFF (since {poss, nec} × {epistemic} is a Cartesian product). -/
def gitksan : ModalInventory where
  language := "Gitksan"
  family := "Tsimshian"
  source := "Matthewson (2013)"
  expressions := [
    ⟨"ima('a)",    [pe, ne]⟩,     -- variable-force epistemic
    ⟨"gat",        [pe, ne]⟩,     -- variable-force epistemic (+ reportative → epistemic)
    ⟨"da'akhlxw",  [pc]⟩,
    ⟨"anook(xw)",  [pd]⟩,
    ⟨"sgi",        [nd, nc]⟩
  ]

theorem gitksan_all_iff : gitksan.allIFF = true := by native_decide
theorem gitksan_size : gitksan.size = 5 := by native_decide

/-- Gitksan's variable-force epistemic modals satisfy both SAV and IFF:
    {poss, nec} × {epistemic} varies on force only (single flavor). -/
theorem gitksan_ima_sav :
    IntensionalSemantics.Modal.Typology.satisfiesSAV [pe, ne] = true := by native_decide

theorem gitksan_ima_is_iff :
    satisfiesIFF [pe, ne] = true := by native_decide

/-- Greek's Prepei violates SAV: it varies on both force and flavor axes. -/
theorem prepei_not_sav :
    IntensionalSemantics.Modal.Typology.satisfiesSAV [ne, pe, nd, nc] = false := by native_decide

-- ============================================================================
-- §4: Korean (Koreanic) — Uegaki et al. (2025)
-- ============================================================================

def korean : ModalInventory where
  language := "Korean"
  family := "Koreanic"
  source := "Uegaki et al. (2025)"
  expressions := [
    ⟨"-napo-",          [ne]⟩,
    ⟨"-keyss-",         [ne]⟩,
    ⟨"-ya + ha-",       [nd, nc]⟩,       -- deontic + teleological(→circ) + circumstantial
    ⟨"ke-",             [ne]⟩,
    ⟨"they-",           [ne]⟩,
    ⟨"-ya + keyss-",    [nd]⟩,
    ⟨"kes.i-coh-",      [nc]⟩,            -- teleological → circumstantial
    ⟨"ci(-to) molun-",  [pe]⟩,
    ⟨"swu(-to) iss-",   [pe, pc]⟩,        -- epistemic + circumstantial
    ⟨"-to + toy-",      [pd, pc]⟩          -- deontic + teleological(→circ)
  ]

theorem korean_all_iff : korean.allIFF = true := by native_decide
theorem korean_size : korean.size = 10 := by native_decide

-- ============================================================================
-- §5: Modern Greek (Indo-European) — Uegaki et al. (2025)
-- ============================================================================

/-- Greek has non-IFF modals: Prepei and Mporei express non-rectangular
    subsets of the meaning space. Prepei covers {(nec,e),(poss,e),(nec,d),(nec,c)}
    which is NOT a Cartesian product (missing (poss,d) and (poss,c)). -/
def greek : ModalInventory where
  language := "Modern Greek"
  family := "Indo-European"
  source := "Uegaki et al. (2025)"
  expressions := [
    ⟨"Prepei", [ne, pe, nd, nc]⟩,    -- NOT IFF: forces={nec,poss}, flavors={e,d,c}
    ⟨"Mporei", [ne, pe, pd, nc, pc]⟩, -- NOT IFF: missing (nec,d)
    ⟨"Isos",   [pe]⟩                  -- IFF (singleton)
  ]

theorem greek_not_all_iff : greek.allIFF = false := by native_decide
theorem greek_size : greek.size = 3 := by native_decide
theorem greek_iff_count : greek.iffCount = 1 := by native_decide

/-- Prepei is NOT IFF: it expresses both forces and all three flavors,
    but does not express (possibility, deontic) or (possibility, circumstantial). -/
theorem greek_prepei_not_iff :
    satisfiesIFF [ne, pe, nd, nc] = false := by native_decide

-- ============================================================================
-- §6: Mandarin (Sino-Tibetan) — Uegaki et al. (2025)
-- ============================================================================

/-- Mandarin has many modals, extensive synonymy, but all satisfy IFF.
    The paper notes Mandarin has three modals all encoding strong ∧ epistemic. -/
def mandarin : ModalInventory where
  language := "Mandarin"
  family := "Sino-Tibetan"
  source := "Uegaki et al. (2025)"
  expressions := [
    ⟨"yīdìng",  [ne]⟩,
    ⟨"bìrán",   [ne]⟩,
    ⟨"juéduì",  [ne]⟩,
    ⟨"bìxū",    [nd, nc]⟩,           -- deontic + teleological(→circ) + circumstantial
    ⟨"yào",     [nd, nc]⟩,           -- same pattern + weak necessity
    ⟨"děi",     [nd, nc]⟩,           -- same pattern
    ⟨"yīnggāi", [ne, nd, nc]⟩,      -- weak necessity across all flavors
    ⟨"dàgài",   [ne]⟩,
    ⟨"kěnéng",  [pe]⟩,
    ⟨"kěyǐ",   [pd, pc]⟩,           -- deontic + teleological(→circ) + circumstantial
    ⟨"yěxǔ",   [pe]⟩,
    ⟨"néng",    [pd, pc]⟩             -- deontic + circumstantial
  ]

theorem mandarin_all_iff : mandarin.allIFF = true := by native_decide
theorem mandarin_size : mandarin.size = 12 := by native_decide
theorem mandarin_has_synonymy : mandarin.hasSynonymy = true := by native_decide

-- ============================================================================
-- §7: Dutch (Indo-European) — Uegaki et al. (2025)
-- ============================================================================

/-- Dutch has one non-IFF modal: zou/zouden...kunnen expresses
    {(nec,e),(poss,e),(poss,c)} which is not Cartesian-closed (missing (nec,c)). -/
def dutch : ModalInventory where
  language := "Dutch"
  family := "Indo-European"
  source := "Uegaki et al. (2025)"
  expressions := [
    ⟨"zal",                     [ne]⟩,
    ⟨"moet/moeten",             [ne, nd, nc]⟩,
    ⟨"zou/zouden...moeten",     [nd, nc]⟩,
    ⟨"kan/kunnen",              [pc]⟩,            -- teleological(→circ) + circumstantial
    ⟨"zou/zouden...kunnen",     [ne, pe, pc]⟩,    -- NOT IFF
    ⟨"waarschijnlijk",          [ne, pe]⟩,         -- variable-force epistemic
    ⟨"zal/zouden waarschijnlijk", [ne]⟩,
    ⟨"moet/moeten eigenlijk",   [nd]⟩,
    ⟨"misschien",               [pe]⟩,
    ⟨"mag/mogen",               [pd]⟩
  ]

theorem dutch_not_all_iff : dutch.allIFF = false := by native_decide
theorem dutch_size : dutch.size = 10 := by native_decide
theorem dutch_iff_count : dutch.iffCount = 9 := by native_decide

-- ============================================================================
-- §8: Hungarian (Uralic) — Uegaki et al. (2025)
-- ============================================================================

def hungarian : ModalInventory where
  language := "Hungarian"
  family := "Uralic"
  source := "Uegaki et al. (2025)"
  expressions := [
    ⟨"kell",          [ne, nd, nc]⟩,    -- strong across all flavors
    ⟨"kellene",       [nd, nc]⟩,         -- weak necessity deontic + teleological(→circ)
    ⟨"muszáj",        [nd, nc]⟩,         -- strong deontic + circumstantial
    ⟨"valószínűleg",  [ne]⟩,             -- weak necessity epistemic
    ⟨"lehet",         [pe]⟩,
    ⟨"-hat/-het",     [pe, pd, pc]⟩,     -- weak across all flavors
    ⟨"tud-",          [pc]⟩,
    ⟨"kép-",          [pc]⟩
  ]

theorem hungarian_all_iff : hungarian.allIFF = true := by native_decide
theorem hungarian_size : hungarian.size = 8 := by native_decide

-- ============================================================================
-- §9: English (Indo-European) — derived from Fragment
-- ============================================================================

open Fragments.English.FunctionWords (AuxEntry can could will would shall should may might must)

/-- English modal inventory, derived from the Fragment (single source of truth).
    Uses `ModalInventory.fromAuxEntries` to extract modals from `AuxEntry` data. -/
def english : ModalInventory :=
  .fromAuxEntries "English" "Indo-European" "Kratzer (1981), Palmer (2001)"
    [can, could, will, would, shall, should, may, might, must]
    AuxEntry.form AuxEntry.modalMeaning

theorem english_all_iff : english.allIFF = true := by native_decide
theorem english_size : english.size = 9 := by native_decide

-- ============================================================================
-- §10: Cross-Linguistic Summary
-- ============================================================================

/-- All nine inventories. -/
def allInventories : List ModalInventory :=
  [tlingit, javanese, gitksan, korean, greek, mandarin, dutch, hungarian, english]

/-- Seven of nine encoded languages have perfect IFF degree (1.0). -/
theorem seven_of_nine_perfect_iff :
    (allInventories.filter (·.allIFF)).length = 7 := by native_decide

/-- All nine languages have IFF degree ≥ 1/3 (the minimum is Greek at 1/3). -/
theorem all_have_some_iff :
    allInventories.all (fun inv => inv.iffCount > 0) = true := by native_decide

-- ============================================================================
-- §11: IFF and Efficient Communication
-- ============================================================================

/-! ## Efficient Communication (Imel, Guo, & Steinert-Threlkeld 2026)

Key computational results (verified over 32,301 generated + 27 natural languages):

1. Every Pareto-optimal modal system consists only of IFF modals.
2. IFF degree correlates positively with simplicity, informativeness,
   and Pareto-optimality.
3. Attested modal systems are more Pareto-optimal than the vast majority
   of hypothetically possible systems (mean optimality: 0.937 vs 0.776). -/

/-- Mean Pareto-optimality of natural languages (Table 6). -/
def naturalMeanOptimality : Float := 0.937

/-- Mean Pareto-optimality of the generated population (Table 6). -/
def populationMeanOptimality : Float := 0.776

theorem natural_more_optimal :
    naturalMeanOptimality > populationMeanOptimality := by native_decide

end Phenomena.Modality.Typology

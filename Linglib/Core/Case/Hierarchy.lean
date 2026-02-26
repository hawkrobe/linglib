import Linglib.Core.Case.Basic

/-!
# Blake's Case Hierarchy @cite{blake-2001}

The **case hierarchy** (Blake 2001, Ch. 2) is an implicational universal over
case inventories:

    NOM/ACC  >  GEN  >  DAT  >  LOC  >  ABL/INST  >  COM/ALL/PERL  >  ...

If a language has a case at position *n* on the hierarchy, it has all cases at
positions 1 through *n* − 1. This is the single most important typological
generalization about case systems.

The hierarchy partitions into three zones:
- **Core** (rank 6): NOM, ACC, ERG, ABS — grammatical relation marking
- **Inner peripheral** (ranks 3–5): GEN, DAT, LOC — common obliques
- **Outer peripheral** (ranks 0–2): ABL, INST, COM, ALL, PERL, etc.

## Contiguity

A valid case inventory has **no gaps** among its peripheral cases: if the
inventory contains cases at ranks *r₁* and *r₂* (with *r₁ < r₂*), then for
every rank *r* with *r₁ < r < r₂*, at least one case at rank *r* is also
in the inventory. Core cases (rank 6) are treated as alternatives at the top
of the hierarchy — a language has NOM/ACC or ERG/ABS (or both in split
systems), but need not have all four.

## References

- Blake, B. J. (2001). *Case* (2nd ed.). Cambridge University Press. Ch. 2.
- Moravcsik, E. A. (1974). Object-verb agreement. *WPLU* 15: 25–140.
- Iggesen, O. A. (2013). Number of Cases. In Dryer & Haspelmath (eds.), WALS.
-/

namespace Core.Case

-- ============================================================================
-- § 1: Hierarchy Rank
-- ============================================================================

/-- Position on Blake's case hierarchy (Blake 2001, Ch. 2).

    Higher rank = more likely to exist in a language's case inventory.

    Ranks are grouped into tiers:
    - 6: core grammatical (NOM, ACC, ERG, ABS) — alternatives, not all required
    - 5: genitive
    - 4: dative
    - 3: locative
    - 2: ablative, instrumental
    - 1: comitative, allative, perlative, benefactive
    - 0: vocative, partitive, causal (sporadic, outside the main hierarchy) -/
def Case.hierarchyRank : Case → Nat
  | .nom | .acc | .erg | .abs => 6
  | .gen                      => 5
  | .dat                      => 4
  | .loc                      => 3
  | .abl | .inst              => 2
  | .com | .all | .perl | .ben => 1
  | .voc | .part | .caus      => 0

-- ============================================================================
-- § 2: Contiguity / Valid Inventory
-- ============================================================================

/-- A case inventory is contiguous (no gaps) on the hierarchy.

    For every pair of cases in the inventory, every case at an intermediate
    rank must also be present. This is Blake's implicational universal: you
    can't have DAT without GEN, or LOC without DAT.

    The check iterates over `Case.allCases` as the universe of possible
    cases. -/
def validInventory (inv : List Case) : Bool :=
  inv.all fun c =>
    inv.all fun c' =>
      -- For every pair (c, c') where c' ranks strictly higher
      if c'.hierarchyRank > c.hierarchyRank then
        -- Every case at an intermediate rank must be present
        Case.allCases.all fun c'' =>
          if c''.hierarchyRank > c.hierarchyRank &&
             c''.hierarchyRank < c'.hierarchyRank then
            inv.any (· == c'')
          else true
      else true

-- ============================================================================
-- § 3: Hierarchy Ordering Theorems
-- ============================================================================

/-- Core cases are at the top of the hierarchy. -/
theorem core_highest : Case.hierarchyRank .nom = 6 := rfl

/-- GEN outranks DAT on the hierarchy. -/
theorem gen_above_dat :
    Case.hierarchyRank .gen > Case.hierarchyRank .dat := by decide

/-- DAT outranks LOC on the hierarchy. -/
theorem dat_above_loc :
    Case.hierarchyRank .dat > Case.hierarchyRank .loc := by decide

/-- LOC outranks ABL/INST on the hierarchy. -/
theorem loc_above_abl :
    Case.hierarchyRank .loc > Case.hierarchyRank .abl := by decide

theorem loc_above_inst :
    Case.hierarchyRank .loc > Case.hierarchyRank .inst := by decide

/-- ABL and INST occupy the same tier. -/
theorem abl_inst_same_rank :
    Case.hierarchyRank .abl = Case.hierarchyRank .inst := rfl

-- ============================================================================
-- § 4: Valid Inventory Examples
-- ============================================================================

/-- A two-case system {NOM, ACC} is valid. -/
theorem two_case_valid :
    validInventory [.nom, .acc] = true := by native_decide

/-- {NOM, ACC, GEN} is valid. -/
theorem three_case_with_gen_valid :
    validInventory [.nom, .acc, .gen] = true := by native_decide

/-- {NOM, ACC, GEN, DAT} is valid. -/
theorem four_case_valid :
    validInventory [.nom, .acc, .gen, .dat] = true := by native_decide

/-- {NOM, ACC, GEN, DAT, LOC} is valid. -/
theorem five_case_valid :
    validInventory [.nom, .acc, .gen, .dat, .loc] = true := by native_decide

/-- {NOM, ACC, GEN, DAT, LOC, ABL, INST} is valid. -/
theorem seven_case_valid :
    validInventory [.nom, .acc, .gen, .dat, .loc, .abl, .inst] = true := by
  native_decide

/-- An ergative core {ERG, ABS, GEN, DAT} is also valid. -/
theorem ergative_four_case_valid :
    validInventory [.erg, .abs, .gen, .dat] = true := by native_decide

/-- Mixed core {NOM, ERG, ABS, GEN} — split-ergative system. -/
theorem split_ergative_valid :
    validInventory [.nom, .erg, .abs, .gen] = true := by native_decide

-- ============================================================================
-- § 5: Invalid Inventory Examples (Contiguity Violations)
-- ============================================================================

/-- {NOM, ACC, DAT} skips GEN — invalid by contiguity. -/
theorem skip_gen_invalid :
    validInventory [.nom, .acc, .dat] = false := by native_decide

/-- {NOM, ACC, LOC} skips GEN and DAT — invalid. -/
theorem skip_gen_dat_invalid :
    validInventory [.nom, .acc, .loc] = false := by native_decide

/-- {NOM, ACC, ABL} skips GEN, DAT, LOC — invalid. -/
theorem skip_to_abl_invalid :
    validInventory [.nom, .acc, .abl] = false := by native_decide

/-- {NOM, ACC, GEN, LOC} skips DAT — invalid. -/
theorem skip_dat_invalid :
    validInventory [.nom, .acc, .gen, .loc] = false := by native_decide

end Core.Case

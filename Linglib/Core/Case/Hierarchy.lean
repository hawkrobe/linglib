import Linglib.Core.Case.Basic

/-!
# Blake's Case Hierarchy @cite{blake-1994}

The **case hierarchy** (Blake 1994, §5.8, example 68) is an implicational
tendency over case inventories:

    NOM  ACC/ERG  GEN  DAT  LOC  ABL/INST  others

If a language has a case at position *n*, it *usually* has at least one case
from each position to the left (Blake 1994, p. 157). Blake hedges this as
holding "with overwhelmingly greater than chance frequency" (borrowing Greenberg
1963). Gaps occur when higher grammatical relations are marked by bound pronouns
or word order (p. 89).

Ranks 6–2 directly encode Blake's hierarchy. Ranks 1 (COM, ALL, PERL, BEN) and
0 (VOC, PART, CAUS) are our assignment within Blake's undifferentiated "others"
— he notes "it is doubtful whether the hierarchy can be developed much further"
beyond ABL/INST (p. 160).

## Contiguity

`validInventory` formalizes the hierarchy as a strict no-gaps predicate: an
idealization of Blake's tendency. Real languages occasionally violate it (e.g.,
Nanai has NOM ACC DAT LOC ABL INST ALL but no GEN — Blake's example 76,
p. 160). The predicate is useful for checking well-formedness of idealized
inventories.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press. §5.8.
- Moravcsik, E. A. (1974). Object-verb agreement. *WPLU* 15: 25–140.
- Iggesen, O. A. (2013). Number of Cases. In Dryer & Haspelmath (eds.), WALS.
-/

namespace Core

-- ============================================================================
-- § 1: Hierarchy Rank
-- ============================================================================

/-- Position on Blake's case hierarchy (Blake 1994, §5.8, ex. 68).

    Higher rank = more likely to exist in a language's case inventory.

    Ranks are grouped into tiers:
    - 6: core grammatical (NOM, ACC, ERG, ABS) — alternatives, not all required
    - 5: genitive
    - 4: dative
    - 3: locative
    - 2: ablative, instrumental
    - 1: comitative, allative, perlative, benefactive (our ranking within
         Blake's undifferentiated "others")
    - 0: vocative, partitive, causal (sporadic, outside the main hierarchy) -/
def Case.hierarchyRank : Case → Nat
  | .nom | .acc | .erg | .abs => 6
  | .gen                      => 5
  | .dat                      => 4
  | .loc                      => 3
  | .abl | .inst              => 2
  | .com | .all | .perl | .ben => 1
  | .voc | .part | .caus | .ess | .transl | .abess => 0

-- ============================================================================
-- § 2: Contiguity / Valid Inventory
-- ============================================================================

/-- Whether the inventory has at least one case at the given rank. -/
def hasRank (inv : List Case) (r : Nat) : Bool :=
  inv.any fun c => c.hierarchyRank == r

/-- A case inventory is contiguous (no rank gaps) on the hierarchy.

    For every pair of cases in the inventory, each intermediate rank must
    have **at least one** representative in the inventory. This matches
    Blake's implicational tendency (1994, §5.8): if a language has cases at
    ranks N and M (N < M), it usually has at least one case at each rank
    between them.

    The predicate does NOT require all cases at a given rank to be present
    — Blake's slash notation (ACC/ERG, ABL/INST) signals alternatives, not
    conjunctions, and a language may have COM without PERL.

    Real languages occasionally violate even this weaker check (e.g.,
    Nanai: Blake 1994, ex. 76, p. 160). -/
def validInventory (inv : List Case) : Bool :=
  inv.all fun c =>
    inv.all fun c' =>
      -- For every pair (c, c') where c' ranks strictly higher
      if c'.hierarchyRank > c.hierarchyRank then
        -- At least one case at each intermediate rank must be present
        let lo := c.hierarchyRank
        let hi := c'.hierarchyRank
        List.range hi |>.all fun r =>
          if r > lo && r < hi then hasRank inv r
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

end Core

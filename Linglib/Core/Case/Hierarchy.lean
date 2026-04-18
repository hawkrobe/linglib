import Mathlib.Order.Lattice
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Case.Basic
/-!
# Blake's Case Hierarchy
@cite{blake-1994}

Implicational hierarchy over case inventories with contiguity checking.
The 9 UD-specific spatial cases all sit at the peripheral spatial tier
(rank 1) since Blake's hierarchy collapses them into a single locative/
spatial group.

Inventory validity is the `Set.OrdConnected`-style contiguity property
expressed in a form `decide` can mechanically check.
-/

namespace Core

/-- Position on Blake's case hierarchy (@cite{blake-1994}, §5.8, ex. 68).

    Higher rank = more likely to exist in a language's case inventory.

    Ranks: 6 = core (NOM/ACC/ERG/ABS), 5 = GEN, 4 = DAT, 3 = LOC,
    2 = ABL/INST, 1 = COM/ALL/PERL/BEN + UD spatial cases (ADE/INE/ILL/ELA/
    SUB/SUP/DEL — Finnish/Hungarian fine-grained spatial),
    0 = VOC/PART/CAUS/ESS/TRANSL/ABESS + UD's TER/TEM (terminative,
    temporal — peripheral non-spatial).

    Codomain is `Fin 7` — the boundedness is encoded in the type, not as a
    separate `*_bounded` theorem. -/
def Case.hierarchyRank : Case → Fin 7
  | .nom | .acc | .erg | .abs => 6
  | .gen                      => 5
  | .dat                      => 4
  | .loc                      => 3
  | .abl | .inst              => 2
  | .com | .all | .perl | .ben
  | .Ade | .Ine | .Ill | .Ela | .Sub | .Sup | .Del => 1
  | .voc | .part | .caus | .ess | .transl | .abess
  | .Ter | .Tem => 0

/-- An inventory is **contiguous** on Blake's hierarchy: every rank between
    two realized ranks is itself realized. Formalizes Blake's implicational
    tendency (1994, §5.8). Equivalent to `Set.OrdConnected` on the rank
    image, expressed here in the form `decide` can mechanically check. -/
def Case.IsValidInventory (inv : Finset Case) : Prop :=
  ∀ r : Fin 7,
    (∃ c ∈ inv, c.hierarchyRank < r) →
    (∃ c ∈ inv, r < c.hierarchyRank) →
    (∃ c ∈ inv, c.hierarchyRank = r)

instance (inv : Finset Case) : Decidable (Case.IsValidInventory inv) := by
  unfold Case.IsValidInventory; infer_instance

theorem two_case_valid :
    Case.IsValidInventory {.nom, .acc} := by decide

theorem three_case_with_gen_valid :
    Case.IsValidInventory {.nom, .acc, .gen} := by decide

theorem four_case_valid :
    Case.IsValidInventory {.nom, .acc, .gen, .dat} := by decide

theorem five_case_valid :
    Case.IsValidInventory {.nom, .acc, .gen, .dat, .loc} := by decide

theorem seven_case_valid :
    Case.IsValidInventory {.nom, .acc, .gen, .dat, .loc, .abl, .inst} := by
  decide

theorem ergative_four_case_valid :
    Case.IsValidInventory {.erg, .abs, .gen, .dat} := by decide

theorem split_ergative_valid :
    Case.IsValidInventory {.nom, .erg, .abs, .gen} := by decide

theorem skip_gen_invalid :
    ¬ Case.IsValidInventory {.nom, .acc, .dat} := by decide

theorem skip_gen_dat_invalid :
    ¬ Case.IsValidInventory {.nom, .acc, .loc} := by decide

theorem skip_to_abl_invalid :
    ¬ Case.IsValidInventory {.nom, .acc, .abl} := by decide

theorem skip_dat_invalid :
    ¬ Case.IsValidInventory {.nom, .acc, .gen, .loc} := by decide

end Core

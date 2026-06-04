import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice
import Mathlib.Tactic.DeriveFintype
import Linglib.Data.UD.Basic

/-!
# Case — Feature Taxonomy
[de-marneffe-zeman-2021] [blake-1994] [stassen-1985]

The `Features.Case` type itself (a definitional alias for `UD.Case`), the
small enums for alignment family / case assignment / fixed encoding, and
Blake's implicational hierarchy over case inventories.

Both naming conventions are valid: `.Nom`/`.Acc` (UD PascalCase) and
`.nom`/`.acc` (theoretical lowercase) refer to the same constructors,
via `@[match_pattern]` abbrevs in `Core/UD.lean`.

## Main declarations

* `Features.Case` — UD-aliased case enum (28 constructors)
* `Features.AlignmentFamily`, `Features.CaseAssignment`,
  `Features.FixedCaseEncoding` — small per-entry feature enums
* `Features.Case.hierarchyRank` — Blake (1994) §5.8 implicational hierarchy
  (`Fin 7`-codomain rank)
* `Features.Case.IsValidInventory` — `Set.OrdConnected`-style contiguity
  predicate, decidable

## Related modules

* `Typology/Case.lean` — WALS case typology (Iggesen et al.)
* `Typology/Alignment.lean` — split ergativity, alignment typology
* `Typology/Comparison.lean` — Stassen comparative-construction typology
* `Syntax/Case/Order.lean` — Caha's nanosyntactic containment order
* `Morphology/Case/Allomorphy.lean` — Bobaljik *ABA + syncretism substrate
* `Diachronic/CaseGrammaticalization.lean` — Heine 2009 cline + extensions
-/

namespace Features

/-! ### Case enum and small companion enums -/

/-- The two major morphosyntactic alignment families. -/
inductive AlignmentFamily where
  | accusative
  | ergative
  deriving DecidableEq, Repr

/-- Cross-linguistic case inventory. **Definitional alias for `UD.Case`** —
    the Universal Dependencies treebank tagset (28 constructors). All
    theoretical machinery (Blake hierarchy, Anderson features, Caha
    containment, Heine grammaticalization) operates over this same type,
    ensuring there is a single source of truth shared between UD-annotated
    lexical data and theoretical analyses. -/
abbrev Case := UD.Case

-- Fintype Case follows from Fintype UD.Case (derived in Core/UD.lean).
deriving instance Fintype for Case

/-! Lowercase `match_pattern` constructor aliases (`.nom`, `.acc`, …) live
    in the canonical `UD.Case` namespace (`Core/UD.lean`). Since
    `Features.Case = UD.Case`, dot-notation `(.nom : Features.Case)` resolves
    through that single source of truth — no separate `Features.Case.*`
    aliases are needed. -/

/-- The 28 UD case constructors are exhaustive. -/
theorem Case.card_univ : (Finset.univ : Finset Case).card = 28 := by decide

/-- How case is assigned to an NP in a given construction
    ([stassen-1985], §2.2.1). -/
inductive CaseAssignment where
  | derived
  | fixed
  deriving DecidableEq, Repr

/-- For fixed-case NPs, what syntactic role the NP occupies. -/
inductive FixedCaseEncoding where
  | directObject
  | adverbial
  deriving DecidableEq, Repr

/-! ### Blake's Case Hierarchy [blake-1994]

Implicational hierarchy over case inventories with contiguity checking.
The 9 UD-specific spatial cases all sit at the peripheral spatial tier
(rank 1) since Blake's hierarchy collapses them into a single locative/
spatial group.

Inventory validity is the `Set.OrdConnected`-style contiguity property
expressed in a form `decide` can mechanically check. -/

/-- Position on Blake's case hierarchy ([blake-1994], §5.8, ex. 68).

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

end Features

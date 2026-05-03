import Linglib.Core.Case.Basic
import Linglib.Core.Case.FeatureBundle
import Linglib.Core.Case.Order
import Linglib.Core.Case.Allomorphy
import Mathlib.Order.BoundedOrder.Basic

/-!
# CaseContainment — Caha-Anchored Residue (Phase 2/3 staging file)

@cite{caha-2009} @cite{anderson-1992} @cite{blake-1994}

This file is **transitional**: it carries the Caha- and Anderson-anchored
material that has not yet been relocated to its final home. The
framework-neutral substrate (`AllomorphyPattern`, `ViolatesABA`,
`IsContiguous`, `HierarchyAdjacent`, `InventoryAdjacent`, syncretism
examples and theorems) has moved to `Core/Case/Allomorphy.lean` (Phase 2).
The remaining content — Anderson 1992 case-feature theorems and the
Caha containment-respect predicate — will dissolve into
`Phenomena/Case/Studies/Caha2009.lean` in Phase 3.
-/

namespace Interfaces.Morphosyntax.CaseContainment

open Core
open Core.Case.Allomorphy (HierarchyAdjacent)

-- ============================================================================
-- § 8: Anderson's Features Explain Syncretism (@cite{anderson-1992})
-- ============================================================================

/-- ERG/INST syncretism: both share the {src} feature despite hierarchy
    non-adjacency. -/
theorem erg_inst_share_src :
    (Case.toCaseRelation .erg).any (CaseFeature.src ∈ ·) ∧
    (Case.toCaseRelation .inst).any (CaseFeature.src ∈ ·) ∧
    ¬ HierarchyAdjacent .erg .inst :=
  ⟨by decide, by decide, by decide⟩

/-- NOM/ACC syncretism (neuter nouns): both contain the abs feature. -/
theorem nom_acc_share_abs :
    (Case.toCaseRelation .nom).any (CaseFeature.abs ∈ ·) ∧
    (Case.toCaseRelation .acc).any (CaseFeature.abs ∈ ·) :=
  ⟨by decide, by decide⟩

/-- ABL/LOC syncretism: both map to {loc}. -/
theorem abl_loc_same_case_relation :
    Case.toCaseRelation .abl = Case.toCaseRelation .loc := rfl

-- ============================================================================
-- § 10: Caha Containment-Respecting Inventories
-- ============================================================================

/-- Does an inventory respect Caha's containment hierarchy? True iff `inv`
    is downward-closed under the canonical `PartialOrder Case` (Caha
    containment): whenever `c ∈ inv` and `d ≤ c`, then `d ∈ inv`.

    Off-hierarchy cases (ERG, ABS, INST, COM, …) impose no constraint —
    in the Caha order, off-hierarchy `c` only has `c ≤ c`, so the
    downward-closure condition is vacuous. On-hierarchy `c` of rank `r`
    forces every lower on-hierarchy case (ranks `0, …, r-1`) into `inv`,
    which is exactly the prefix-contiguity Caha demands.

    This is the standard "lower set" predicate from order theory, applied
    to the Caha order extracted in `Core/Case/Order.lean`. -/
def RespectsCahaContainment (inv : Finset Case) : Prop :=
  ∀ c ∈ inv, ∀ d, d ≤ c → d ∈ inv

instance (inv : Finset Case) : Decidable (RespectsCahaContainment inv) := by
  unfold RespectsCahaContainment; infer_instance

end Interfaces.Morphosyntax.CaseContainment

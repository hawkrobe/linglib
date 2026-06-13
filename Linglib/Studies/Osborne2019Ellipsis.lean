import Linglib.Syntax.DependencyGrammar.Formal.Ellipsis
import Linglib.Studies.Steedman2000

/-!
# Bridge: DG Ellipsis → Steedman's Ellipsis Taxonomy
[osborne-2019]

Maps the DG catena-based ellipsis taxonomy to [steedman-2000]'s ellipsis
types (`Steedman2000.EllipsisType`).

Key result: gapping (from Steedman's taxonomy) is a special case of
catena-ellipsis — the elided verb is always a singleton catena that is
not a constituent.

## Bridges

- `DepGrammar.Ellipsis.EllipsisType` → `Steedman2000.EllipsisType`
- `DepGrammar.Ellipsis.gappingTree` / `gappingElided` → catena-not-constituent proof
-/

namespace DepGrammar.Ellipsis

open DepGrammar Catena

/-- Map DG ellipsis types to `Steedman2000.EllipsisType`.
    Not all DG types have Steedman equivalents (pseudogapping/fragmentAnswer don't). -/
def toGappingEllipsisType :
    EllipsisType → Option Steedman2000.EllipsisType
  | .vpEllipsis => some .vpEllipsis
  | .gapping => some .gapping
  | .stripping => some .stripping
  | .sluicing => some .sluicing
  | .pseudogapping => none  -- No Steedman2000 equivalent
  | .fragmentAnswer => none  -- No Steedman2000 equivalent

/-- Gapping (from Steedman's taxonomy) is a special case of catena-ellipsis.
    The verb alone is elided — always a singleton catena. -/
theorem catena_ellipsis_subsumes_gapping :
    toGappingEllipsisType .gapping = some .gapping := rfl

/-- Gapping always elides a non-constituent catena: the verb alone is a
    catena (trivially) but never a constituent (its subtree includes
    subject and object). -/
theorem gapping_always_catena_not_constituent :
    isCatena gappingTree.deps gappingElided = true ∧
    isConstituent gappingTree.deps 3 gappingElided = false := by
  constructor <;> native_decide

end DepGrammar.Ellipsis

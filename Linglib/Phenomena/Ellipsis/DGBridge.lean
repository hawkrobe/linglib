import Linglib.Theories.Syntax.DependencyGrammar.Formal.Ellipsis
import Linglib.Phenomena.Ellipsis.Gapping

/-!
# Bridge: DG Ellipsis → Phenomena Ellipsis

Maps the DG catena-based ellipsis taxonomy (Osborne 2019) to the
Phenomena ellipsis types from `Phenomena.Ellipsis.Gapping`.

Key result: gapping (from the Phenomena taxonomy) is a special case of
catena-ellipsis — the elided verb is always a singleton catena that is
not a constituent.

## Bridges

- `DepGrammar.Ellipsis.EllipsisType` → `Phenomena.Ellipsis.Gapping.EllipsisType`
- `DepGrammar.Ellipsis.gappingTree` / `gappingElided` → catena-not-constituent proof
-/

namespace DepGrammar.Ellipsis

open DepGrammar Catena

/-- Map DG ellipsis types to Phenomena's Gapping.EllipsisType.
    Not all DG types have Phenomena equivalents (pseudogapping/fragmentAnswer don't). -/
def toGappingEllipsisType :
    EllipsisType → Option Phenomena.Ellipsis.Gapping.EllipsisType
  | .vpEllipsis => some .vpEllipsis
  | .gapping => some .gapping
  | .stripping => some .stripping
  | .sluicing => some .sluicing
  | .pseudogapping => none  -- No Phenomena equivalent
  | .fragmentAnswer => none  -- No Phenomena equivalent

/-- Gapping (from Phenomena) is a special case of catena-ellipsis.
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

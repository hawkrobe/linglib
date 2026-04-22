import Linglib.Theories.Syntax.DependencyGrammar.Formal.Islands
import Linglib.Phenomena.Islands.Studies.Ross1967

/-!
# Bridge: DG Islands → Phenomena Island Constraints
@cite{osborne-2019} @cite{ross-1967}

Maps the DG rising-catena island taxonomy from @cite{osborne-2019} to the
Phenomena island constraint types from `Phenomena.Islands.Studies.Ross1967`.

Three of Osborne's island types have direct Phenomena equivalents:
- adjunct → .adjunct
- subject → .subject
- wh-island → .embeddedQuestion

The remaining types (leftBranch, specifiedNP, rightRoof, pStranding,
piedPiping) are DG-specific and map to `none`.
-/

namespace Phenomena.Islands.Studies.Osborne2019

open DepGrammar.Islands (OsborneIslandType)

/-- Map `OsborneIslandType` to `ConstraintType` for the shared types. -/
def toPhenomenaConstraintType :
    OsborneIslandType → Option ConstraintType
  | .adjunct       => some .adjunct
  | .subject       => some .subject
  | .whIsland      => some .embeddedQuestion
  | _              => none

end Phenomena.Islands.Studies.Osborne2019

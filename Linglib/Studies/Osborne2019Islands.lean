import Linglib.Syntax.DependencyGrammar.Formal.Islands
import Linglib.Studies.Ross1967

/-!
# Bridge: DG Islands → Ross 1967 Island Constraints
[osborne-2019] [ross-1967]

Maps the DG rising-catena island taxonomy from [osborne-2019] to the
island `ConstraintType` taxonomy from `Studies/Ross1967`.

Three of Osborne's island types have direct `ConstraintType` equivalents:
- adjunct → .adjunct
- subject → .subject
- wh-island → .embeddedQuestion

The remaining types (leftBranch, specifiedNP, rightRoof, pStranding,
piedPiping) are DG-specific and map to `none`.
-/

namespace Osborne2019Islands

open DepGrammar.Islands (OsborneIslandType)

/-- Map `OsborneIslandType` to `ConstraintType` for the shared types. -/
def toRossConstraintType :
    OsborneIslandType → Option ConstraintType
  | .adjunct       => some .adjunct
  | .subject       => some .subject
  | .whIsland      => some .embeddedQuestion
  | _              => none

end Osborne2019Islands

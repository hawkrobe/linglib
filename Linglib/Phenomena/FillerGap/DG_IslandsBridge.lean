import Linglib.Theories.Syntax.DependencyGrammar.Formal.Islands
import Linglib.Phenomena.FillerGap.Islands.Data

/-!
# Bridge: DG Islands → Phenomena Island Constraints
@cite{hofmeister-sag-2010} @cite{osborne-2019} @cite{ross-1967}

Maps the DG rising-catena island taxonomy (Osborne 2019, Ch 9) to the
Phenomena island constraint types from `Phenomena.FillerGap.Islands.Data`.

Three of Osborne's island types have direct Phenomena equivalents:
- adjunct → .adjunct
- subject → .subject
- wh-island → .embeddedQuestion

The remaining types (leftBranch, specifiedNP, rightRoof, pStranding,
piedPiping) are DG-specific and map to `none`.

-/

namespace DepGrammar.Islands

/-- Map `OsborneIslandType` to `ConstraintType` for the shared types. -/
def toPhenomenaConstraintType :
    OsborneIslandType → Option ConstraintType
  | .adjunct       => some .adjunct
  | .subject       => some .subject
  | .whIsland      => some .embeddedQuestion
  | _              => none

end DepGrammar.Islands

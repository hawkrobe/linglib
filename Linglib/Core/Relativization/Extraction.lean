import Linglib.Core.Relativization.Basic
import Linglib.Core.ExtractionMorphology

/-!
# Bridge: Extraction Morphology ↔ Accessibility Hierarchy
@cite{keenan-comrie-1977}

Maps between `ExtractionTarget` (5 structural positions from extraction
morphology) and `AHPosition` (6 positions on the Accessibility Hierarchy).

The two type systems encode overlapping Ā-movement phenomena:
- `ExtractionTarget` focuses on *where* extraction occurs (used by extraction
  morphology fragments for Mayan, Austronesian, Celtic languages)
- `AHPosition` focuses on *what can be relativized* (used by relativization
  fragments and the @cite{keenan-comrie-1977} hierarchy constraints)

The bridge is partial: `AHPosition.objComparison` has no standard
`ExtractionTarget` equivalent (object of comparison is a position specific
to the relativization literature). In the other direction, `possessor`
maps to `genitive`.
-/

namespace Core

open Interfaces

-- ============================================================================
-- § 1: ExtractionTarget → AHPosition
-- ============================================================================

/-- Map an extraction target to its AH position. Possessor extraction
    corresponds to the genitive position on the AH. -/
def extractionTargetToAH : ExtractionTarget → AHPosition
  | .subject        => .subject
  | .directObject   => .directObject
  | .indirectObject => .indirectObject
  | .oblique        => .oblique
  | .possessor      => .genitive

-- ============================================================================
-- § 2: AHPosition → ExtractionTarget (partial)
-- ============================================================================

/-- Map an AH position to an extraction target (partial: object of comparison
    has no standard ExtractionTarget equivalent). -/
def ahToExtractionTarget : AHPosition → Option ExtractionTarget
  | .subject        => some .subject
  | .directObject   => some .directObject
  | .indirectObject => some .indirectObject
  | .oblique        => some .oblique
  | .genitive       => some .possessor
  | .objComparison  => none

-- ============================================================================
-- § 3: Roundtrip Theorems
-- ============================================================================

/-- Round-tripping ExtractionTarget → AH → ExtractionTarget is the identity
    for all 5 extraction targets. -/
theorem extraction_ah_roundtrip :
    let targets := [ExtractionTarget.subject, .directObject,
                    .indirectObject, .oblique, .possessor]
    targets.all (λ t => ahToExtractionTarget (extractionTargetToAH t) == some t)
      = true := by
  native_decide

/-- Round-tripping AH → ExtractionTarget → AH is the identity for all
    positions except `.objComparison` (which has no ExtractionTarget). -/
theorem ah_extraction_roundtrip :
    let positions := [AHPosition.subject, .directObject, .indirectObject,
                      .oblique, .genitive]
    positions.all (λ p =>
      match ahToExtractionTarget p with
      | some t => extractionTargetToAH t == p
      | none   => false)  -- objComparison excluded
      = true := by
  native_decide

/-- `.objComparison` is the only AH position without an ExtractionTarget. -/
theorem objComparison_no_extraction_target :
    ahToExtractionTarget .objComparison = none := rfl

/-- All other AH positions have ExtractionTarget equivalents. -/
theorem non_ocomp_have_extraction_target :
    let positions := [AHPosition.subject, .directObject, .indirectObject,
                      .oblique, .genitive]
    positions.all (λ p => (ahToExtractionTarget p).isSome) = true := by
  native_decide

end Core

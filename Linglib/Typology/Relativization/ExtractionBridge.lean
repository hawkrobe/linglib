import Linglib.Core.Relativization.Basic
import Linglib.Typology.Extraction

/-!
# Extraction Morphology ↔ Accessibility Hierarchy Bridge
@cite{keenan-comrie-1977}

Maps between `Typology.ExtractionTarget` (5 structural positions from
extraction morphology, defined in `Typology/Extraction.lean`) and
`Core.AHPosition` (6 positions on the @cite{keenan-comrie-1977}
Accessibility Hierarchy).

Both type systems encode overlapping Ā-movement phenomena: extraction
focuses on *where* extraction occurs (used by Mayan, Austronesian,
Celtic Fragments); the AH focuses on *what can be relativized* (used
by relativization Fragments and the Keenan-Comrie hierarchy
constraints). The bridge is partial: `AHPosition.objComparison` (object
of comparison, specific to the relativization literature) has no
standard `ExtractionTarget` equivalent. In the other direction,
`ExtractionTarget.possessor` maps to `AHPosition.genitive`.
-/

namespace Typology.Relativization

open Core (AHPosition)
open Typology (ExtractionTarget)

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

/-- Map an AH position to an extraction target (partial:
    `objComparison` has no standard `ExtractionTarget` equivalent). -/
def ahToExtractionTarget : AHPosition → Option ExtractionTarget
  | .subject        => some .subject
  | .directObject   => some .directObject
  | .indirectObject => some .indirectObject
  | .oblique        => some .oblique
  | .genitive       => some .possessor
  | .objComparison  => none

-- ============================================================================
-- § 3: Roundtrip Theorems (compile-time exhaustive over constructors)
-- ============================================================================

/-- ExtractionTarget → AH → ExtractionTarget is the identity. -/
theorem extraction_ah_roundtrip (t : ExtractionTarget) :
    ahToExtractionTarget (extractionTargetToAH t) = some t := by
  cases t <;> rfl

/-- AH → ExtractionTarget → AH is the identity for every position
    except `objComparison` (which has no `ExtractionTarget`). -/
theorem ah_extraction_roundtrip (p : AHPosition) (h : p ≠ .objComparison) :
    ∃ t, ahToExtractionTarget p = some t ∧ extractionTargetToAH t = p := by
  cases p with
  | objComparison => exact absurd rfl h
  | subject => exact ⟨.subject, rfl, rfl⟩
  | directObject => exact ⟨.directObject, rfl, rfl⟩
  | indirectObject => exact ⟨.indirectObject, rfl, rfl⟩
  | oblique => exact ⟨.oblique, rfl, rfl⟩
  | genitive => exact ⟨.possessor, rfl, rfl⟩

/-- `objComparison` is the only AH position without an `ExtractionTarget`. -/
theorem objComparison_no_extraction_target :
    ahToExtractionTarget .objComparison = none := rfl

/-- Every non-`objComparison` AH position has an `ExtractionTarget` equivalent. -/
theorem non_ocomp_have_extraction_target (p : AHPosition) (h : p ≠ .objComparison) :
    (ahToExtractionTarget p).isSome := by
  cases p <;> first | rfl | exact absurd rfl h

end Typology.Relativization

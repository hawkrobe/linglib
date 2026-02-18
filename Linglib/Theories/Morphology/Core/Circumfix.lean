import Linglib.Core.MorphRule

/-!
# Circumfixal Exponence

Circumfixal exponence wraps a stem with morphological material on both sides
(prefix + suffix). This is a theory-neutral description of the surface
pattern — how a circumfix *arises* (head movement in DM, readjustment rules
in other frameworks) is left to theory-specific modules.

Cross-linguistically attested circumfixes include:
- German past participle *ge-...-t* (ge-mach-t)
- Tigrinya negative *ʔay-...-n* (ʔay-stem-n)
- Malay *ke-...-an* (ke-baik-an "goodness")

## Connections

- **Core/MorphRule.lean**: `AttachmentSide.circumfix` — morphological classification
- **DM/Fission.lean**: Distributed Morphology operations (theory-specific derivation)

## References

- Spencer, A. & A. Zwicky (1998). The Handbook of Morphology. Blackwell.
-/

namespace Morphology.Circumfix

open Core.Morphology (AttachmentSide)

/-- Circumfixal exponence: a stem is wrapped by a prefix and suffix.

    This is a surface-level description of the morphological pattern,
    neutral between theories of how the circumfix arises (head movement,
    readjustment, templatic morphology, etc.).

    For example, German past participle ge-mach-t:
    - `prefix_` = "ge-"
    - `suffix_` = "-t"
    - `stem` = "mach" -/
structure CircumfixExponence where
  /-- Morphological material before the stem -/
  prefix_ : String
  /-- Morphological material after the stem -/
  suffix_ : String
  /-- The verbal stem that gets wrapped -/
  stem : String
  /-- Description of the source of the circumfix -/
  gloss : String := ""
  deriving Repr, DecidableEq, BEq

/-- Apply circumfixal exponence to produce the surface form. -/
def CircumfixExponence.realize (c : CircumfixExponence) : String :=
  c.prefix_ ++ c.stem ++ c.suffix_

/-- A circumfix is discontinuous: its exponents are separated by the stem. -/
def CircumfixExponence.isDiscontinuous (_c : CircumfixExponence) : Bool := true

/-- The attachment side of a circumfix is `AttachmentSide.circumfix`. -/
def CircumfixExponence.attachmentSide (_c : CircumfixExponence) : AttachmentSide :=
  .circumfix

-- ============================================================================
-- Bridge theorems
-- ============================================================================

/-- Every circumfix has the correct attachment side. -/
theorem circumfix_attachment (c : CircumfixExponence) :
    c.attachmentSide = .circumfix := rfl

/-- Every circumfix is discontinuous. -/
theorem circumfix_discontinuous (c : CircumfixExponence) :
    c.isDiscontinuous = true := rfl

/-- The surface form of a circumfix is prefix + stem + suffix. -/
theorem circumfix_realize_concat (c : CircumfixExponence) :
    c.realize = c.prefix_ ++ c.stem ++ c.suffix_ := rfl

-- ============================================================================
-- Examples
-- ============================================================================

/-- German past participle ge-...-t. -/
def germanPastParticiple (stem : String) : CircumfixExponence where
  prefix_ := "ge-"
  suffix_ := "-t"
  stem := stem
  gloss := "PTCP"

/-- German past participle surfaces correctly. -/
theorem german_pp_example :
    (germanPastParticiple "mach").realize = "ge-mach-t" := rfl

end Morphology.Circumfix

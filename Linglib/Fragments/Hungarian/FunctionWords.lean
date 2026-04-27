import Linglib.Theories.Syntax.Minimalism.ExtendedProjection.Basic

/-!
# Hungarian Function Words Fragment
@cite{egressy-2026}

Closed-class functional items relevant to Hungarian clause structure.

## Complementizer *hogy*

The complementizer *hogy* 'that' is the key structural marker in @cite{egressy-2026}: its presence signals a full CP complement (phase boundary, opaque
to tense Agree), while its absence signals a bare TP complement
(transparent to tense Agree).

Unlike English *that*, Hungarian *hogy* is **not optional** in finite
complement clauses — its presence or absence correlates with genuine
structural differences in complement size, not merely with register or
style.

-/

namespace Fragments.Hungarian.FunctionWords

open Minimalism (ComplementSize Cat)

/-- Hungarian complementizer entry. -/
structure HungarianCompEntry where
  /-- Surface form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- The complement size this complementizer projects -/
  complementSize : ComplementSize
  /-- Is the complementizer obligatory in its context? -/
  obligatory : Bool := true
  deriving Repr, BEq

/-- *hogy* 'that' — complementizer projecting a full CP.
    @cite{egressy-2026}: *hogy*-clauses constitute CP phase boundaries,
    blocking upward Agree for [uPAST]. -/
def hogy : HungarianCompEntry where
  form := "hogy"
  gloss := "that"
  complementSize := .cP
  obligatory := true

/-- *hogy* projects a CP (phase-sized, opaque to tense Agree). -/
theorem hogy_projects_cp :
    hogy.complementSize = .cP := rfl

/-- *hogy*-complements are opaque to tense Agree. -/
theorem hogy_opaque :
    hogy.complementSize.transparentToTenseAgree = false := by decide

/-- *hogy* is obligatory (not optional like English "that"). -/
theorem hogy_obligatory :
    hogy.obligatory = true := rfl


end Fragments.Hungarian.FunctionWords

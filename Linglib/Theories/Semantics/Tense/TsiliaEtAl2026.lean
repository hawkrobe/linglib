import Linglib.Core.Presupposition
import Linglib.Core.Reichenbach
import Linglib.Theories.Semantics.Tense.Basic

/-!
# Tsilia, Zhao & Sharvit (2026): Tense and Perspective
@cite{tsilia-zhao-sharvit-2026}

The cross-linguistic incompatibility of temporal ⌈then⌉ with shifted present
tense is derived from **tense presuppositions** anchored to a perspectival
parameter π. This creates the architecturally significant import edge from
tense theory to `Core.Presupposition`.

## Core Insight

Tenses are presupposition triggers:
- PRES presupposes R = P (reference time = perspective time)
- PAST presupposes R < P

OP_π shifts the perspective parameter to the local evaluation time. ⌈then⌉
presupposes that π has been shifted away from the default (P ≠ S) AND that
R = P. The incompatibility arises because OP_π forces P = local evaluation
time, while ⌈then⌉ requires P ≠ local evaluation time — a direct
contradiction.

## Connection to Sharvit (2003)

Sharvit's simultaneous tense is the special case where the embedded tense
presupposition is trivially satisfied at the shifted perspective: the
simultaneous reading has R = P' where P' = E_matrix, which satisfies
the PRES presupposition at the shifted π.

## References

- Tsilia, D., Zhao, Z. & Sharvit, Y. (2026). Tense and perspective.
- Sharvit, Y. (2003). Embedded tense and universal grammar. LI 34(4).
- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels. MIT diss.
-/

namespace Semantics.Tense.TsiliaEtAl2026

open Core.Reichenbach
open Core.Presupposition
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § 1. Tense Presuppositions
-- ════════════════════════════════════════════════════════════════

/-- PRES presupposes R = P: the reference time equals the perspective time.
    This is a point-approximation of the paper's t ○ π overlap condition. -/
def presPresup {Time : Type*} (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime = f.perspectiveTime

/-- PAST presupposes R < P: the reference time precedes the perspective time. -/
def pastPresup {Time : Type*} [LT Time] (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime < f.perspectiveTime

/-- The PRES presupposition is definitionally equal to `isPresent`. -/
theorem presPresup_iff_isPresent {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time) :
    presPresup f ↔ f.isPresent := Iff.rfl

/-- The PAST presupposition is definitionally equal to `isPast`. -/
theorem pastPresup_iff_isPast {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time) :
    pastPresup f ↔ f.isPast := Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § 2. OP_π: Perspective-Shifting Operator
-- ════════════════════════════════════════════════════════════════

/-- OP_π shifts the perspective time to a new value.
    Under attitude verbs, this sets P' = E_matrix (the matrix event time),
    so that embedded tenses are evaluated relative to the attitude time. -/
def opPi {Time : Type*} (f : ReichenbachFrame Time) (newPi : Time) :
    ReichenbachFrame Time :=
  { f with perspectiveTime := newPi }

/-- OP_π corresponds to `embeddedFrame` when shifting to the matrix event time.
    `embeddedFrame` already sets `perspectiveTime := matrixFrame.eventTime`. -/
theorem opPi_eq_embeddedFrame {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
    opPi { speechTime := matrixFrame.speechTime
           perspectiveTime := matrixFrame.speechTime
           referenceTime := embeddedR
           eventTime := embeddedE }
         matrixFrame.eventTime =
    embeddedFrame matrixFrame embeddedR embeddedE := by
  simp [opPi, embeddedFrame]


-- ════════════════════════════════════════════════════════════════
-- § 3. ⌈then⌉ Presupposition
-- ════════════════════════════════════════════════════════════════

/-- ⌈then⌉ presupposes:
    1. R = P (overlap with perspective — same as PRES)
    2. P ≠ S (perspective has been shifted from default)

    The second conjunct captures the anaphoric/non-default requirement:
    ⌈then⌉ requires a contextually shifted perspective point. -/
def thenPresup {Time : Type*} (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime = f.perspectiveTime ∧ f.perspectiveTime ≠ f.speechTime


-- ════════════════════════════════════════════════════════════════
-- § 4. Deleted vs. Shifted Tense
-- ════════════════════════════════════════════════════════════════

/-- Status of an embedded tense morpheme. -/
inductive EmbeddedTenseStatus where
  /-- Tense present with presupposition anchored to shifted π -/
  | shifted
  /-- Tense deleted by SOT; no temporal presupposition -/
  | deleted
  deriving DecidableEq, Repr, BEq

/-- A shifted tense retains its presupposition (PRES or PAST relative to π). -/
def shiftedTensePresup {Time : Type*} [LT Time]
    (f : ReichenbachFrame Time) (isPres : Bool) : Prop :=
  if isPres then presPresup f else pastPresup f

/-- A deleted tense has no temporal presupposition — trivially satisfied. -/
theorem deletedTensePresup : True := trivial


-- ════════════════════════════════════════════════════════════════
-- § 5. Core Incompatibility Theorems
-- ════════════════════════════════════════════════════════════════

/-- General then-perspective incompatibility:
    OP_π sets P = localEval, ⌈then⌉ requires P ≠ localEval → contradiction.

    The root-clause case (in `ThenPresentBridge.lean`) has localEval = S
    and hOP = isSimpleCase. The embedded case has localEval = attitudeTime
    and hOP comes from OP_π. -/
theorem then_perspective_clash {Time : Type*}
    (f : ReichenbachFrame Time) (localEval : Time)
    (hOP : f.perspectiveTime = localEval)
    (hThen : f.perspectiveTime ≠ localEval)
    : False := hThen hOP

/-- ⌈then⌉ + deleted tense → compatible.
    Deleted tense has no presupposition, so OP_π is not required,
    and ⌈then⌉ can freely set P to a contextually salient past time. -/
theorem then_deleted_tense_compatible {Time : Type*}
    (f : ReichenbachFrame Time)
    (hShifted : f.perspectiveTime ≠ f.speechTime)
    (hOverlap : f.referenceTime = f.perspectiveTime)
    : thenPresup f := ⟨hOverlap, hShifted⟩


-- ════════════════════════════════════════════════════════════════
-- § 6. Bridge to PrProp
-- ════════════════════════════════════════════════════════════════

/-- Wrap PRES presupposition as a `PrProp`, showing how tense presuppositions
    compose with the existing presupposition projection system. -/
def presAsPrProp {Time : Type*} [DecidableEq Time]
    (f : ReichenbachFrame Time) : PrProp Unit where
  presup := λ () => decide (f.referenceTime = f.perspectiveTime)
  assertion := λ () => true

/-- The `PrProp` encoding is defined iff the PRES presupposition holds. -/
theorem presAsPrProp_defined_iff {Time : Type*} [DecidableEq Time]
    (f : ReichenbachFrame Time) :
    (presAsPrProp f).presup () = true ↔ f.referenceTime = f.perspectiveTime := by
  simp [presAsPrProp, decide_eq_true_eq]


-- ════════════════════════════════════════════════════════════════
-- § 7. Identity Card + Sharvit Bridge
-- ════════════════════════════════════════════════════════════════

/-- Tsilia, Zhao & Sharvit (2026) identity card.
    The theory treats tenses as presupposition triggers (the key innovation)
    and uses SOT deletion for the then-deleted tense compatibility. -/
def TsiliaEtAl2026 : TenseTheory where
  name := "Tsilia, Zhao & Sharvit 2026"
  citation := "Tsilia, D., Zhao, Z. & Sharvit, Y. (2026). Tense and perspective."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := true
  hasPresuppositionalTense := true
  simultaneousMechanism := "tense presuppositions anchored to perspective parameter π"

/-- The Sharvit (2003) simultaneous reading is the special case where a PRES
    presupposition is trivially satisfied at the shifted perspective.
    `simultaneousFrame` has R = P' = E_matrix, satisfying presPresup. -/
theorem sharvit_simultaneous_satisfies_presPresup {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    presPresup (simultaneousFrame matrixFrame embeddedE) := by
  rfl


end Semantics.Tense.TsiliaEtAl2026

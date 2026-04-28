import Linglib.Theories.Semantics.Tense.Basic

/-!
# @cite{von-stechow-2009}: Tenses in Compositional Semantics
@cite{von-stechow-2009}

@cite{von-stechow-2009}'s theory: tense features are checked against a
local evaluation time that shifts under attitude embedding. The key
mechanism is **feature checking**: tense morphology bears a feature
([PAST], [PRES]) that must be checked against the local temporal
anchor.

## Core Mechanisms

1. **Feature checking** = `GramTense.constrains` (substrate primitive
   in `Core/Time/Tense.lean`). The "checking" terminology is von
   Stechow's; the underlying predicate is the framework-neutral
   `feature.constrains refTime evalTime`.
2. **Perspective shift** = `embeddedFrame` (substrate primitive in
   `Theories/Semantics/Tense/Basic.lean`). The attitude verb sets the
   embedded eval time = matrix E. von Stechow calls this "perspective
   shift"; the operation is the framework-neutral `embeddedFrame
   matrixFrame embeddedR embeddedE`.
3. **SOT as feature checking**: simultaneous reading = [PRES] checked
   against matrix E (no deletion, no ambiguity).

## Architectural Note

After the 0.230.452 wrapper-trim and the Phase E 0.230.456 split, this
file has no concept-file companion in `Theories/Semantics/Tense/`.
@cite{von-stechow-2009}'s contribution is *terminological* — the
"feature checking" name for what is structurally `GramTense.constrains`
applied at a `embeddedFrame`-shifted eval time. The substrate lives
entirely in `Core.Time.Tense` and `Semantics.Tense.Basic`; this file
collects the paper-attributed theorems.

## Advantages Over Abusch

- Handles relative clause tense: feature checking works in relative
  clauses where the perspective time is the modified NP's temporal
  coordinate, not the matrix event time.
- Cleaner compositional architecture: no res movement needed.

-/

namespace Phenomena.TenseAspect.Studies.VonStechow2009

open Core.Time.Tense
open Core.Time.Reichenbach
open Core.Time
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- @cite{von-stechow-2009} derives the shifted reading: [PAST] feature
    checked against matrix E. The embedded reference time is before
    the matrix event time. -/
theorem vonStechow_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (hPast : GramTense.constrains .past embeddedR matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast]
  exact hPast

/-- @cite{von-stechow-2009} derives the simultaneous reading: [PRES]
    feature checked against matrix E. The embedded reference time
    equals the matrix event time — no deletion rule needed. -/
theorem vonStechow_derives_simultaneous {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    (embeddedFrame matrixFrame matrixFrame.eventTime embeddedE).isPresent := by
  simp only [embeddedFrame, ReichenbachFrame.isPresent]

/-- @cite{von-stechow-2009} derives double-access: [PRES] feature under
    past attitude verb. The present tense is checked against matrix E,
    but its indexical nature also requires truth at speech time. -/
theorem vonStechow_derives_double_access {Time : Type*}
    (matrixFrame : ReichenbachFrame Time)
    (p : Time → Prop)
    (h_matrix : p matrixFrame.eventTime)
    (h_speech : p matrixFrame.speechTime) :
    p matrixFrame.eventTime ∧ p matrixFrame.speechTime :=
  ⟨h_matrix, h_speech⟩

/-- @cite{von-stechow-2009} derives relative clause tense: the
    perspective time in a relative clause is the modified NP's
    temporal coordinate, not necessarily the matrix event time.
    Feature checking works uniformly regardless of the source of the
    eval time.

    This is where von Stechow has an advantage over @cite{abusch-1997}:
    feature checking does not require attitude semantics or res
    movement — any eval time source works. -/
theorem vonStechow_derives_relative_clause {Time : Type*} [LinearOrder Time]
    (rcPerspective : Time) (rcRefTime : Time)
    (hPast : GramTense.constrains .past rcRefTime rcPerspective) :
    rcRefTime < rcPerspective :=
  hPast


-- ════════════════════════════════════════════════════════════════
-- § Bridge to TensePronoun
-- ════════════════════════════════════════════════════════════════

/-- @cite{von-stechow-2009}'s feature checking IS
    `TensePronoun.fullPresupposition` when the eval time resolves to
    the same value. -/
theorem feature_checking_is_fullPresupposition {Time : Type*} [LinearOrder Time]
    (tp : TensePronoun) (g : TemporalAssignment Time) :
    GramTense.constrains tp.constraint (tp.resolve g) (tp.evalTime g) ↔
    tp.fullPresupposition g :=
  Iff.rfl


end Phenomena.TenseAspect.Studies.VonStechow2009

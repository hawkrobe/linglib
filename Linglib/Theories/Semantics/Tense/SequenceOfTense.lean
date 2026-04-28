import Linglib.Theories.Semantics.Tense.Compositional
import Linglib.Theories.Semantics.Attitudes.SituationDependent
import Linglib.Theories.Semantics.Tense.Basic

/-!
# Sequence of Tense: TC ↔ IS Bridge
@cite{heim-kratzer-1998} @cite{kratzer-1998} @cite{reichenbach-1947} @cite{von-stechow-2009}

Bridge theorems connecting the truth-conditional tense operators
(`applyTense` from `TC/Tense/Basic.lean`) to the intensional semantic
embedding infrastructure (`embeddedFrame`, `simultaneousFrame`, etc.
from `IS/Tense/Basic.lean`).

Also bridges the situation-semantic formulation of attitude accessibility
(`temporallyBound` from `IS/Attitude/SituationDependent.lean`) to the
Reichenbach frame analysis.

## Core Embedding Infrastructure

The embedding infrastructure (embedded frames, SOT readings, upper limit
constraint) lives in `Theories/Semantics.Intensional/Tense/Basic.lean`.
This file provides the bridge between that infrastructure and the
truth-conditional tense operators.

For the full six-theory comparison (Abusch, Von Stechow, Kratzer, Ogihara,
Klecha, Deal), see `Theories/Semantics.Intensional/Tense/` and
`Comparisons/TenseTheories.lean`.

-/

namespace Semantics.Tense.SequenceOfTense

open Core.Time.Reichenbach
open Semantics.Tense (applyTense)
open Semantics.Tense (embeddedFrame simultaneousFrame)


-- ════════════════════════════════════════════════════════════════
-- § Bridge: applyTense + embeddedFrame
-- ════════════════════════════════════════════════════════════════

/-!
### Connecting applyTense to the Embedding Infrastructure

`applyTense` (truth-conditional) and `embeddedFrame` (intensional semantic)
are defined in different layers. The following theorems bridge them,
showing that the TC tense operators interact correctly with the IS
perspective-shift mechanism.
-/

/-- Applying embedded PAST to the embedded frame means R' < E_matrix.

    The shifted reading: the embedded tense really is PAST relative
    to the shifted perspective (matrix event time). -/
theorem embeddedPast_means_before_matrix {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
    applyTense .past (embeddedFrame matrixFrame embeddedR embeddedE) ↔
    embeddedR < matrixFrame.eventTime := by
  simp only [applyTense, embeddedFrame]

/-- Applying embedded PRESENT to the embedded frame means R' = E_matrix.

    The simultaneous reading: the embedded tense is PRESENT relative
    to the shifted perspective. -/
theorem embeddedPresent_means_at_matrix {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
    applyTense .present (embeddedFrame matrixFrame embeddedR embeddedE) ↔
    embeddedR = matrixFrame.eventTime := by
  simp only [applyTense, embeddedFrame]


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Attitude Accessibility ↔ Reichenbach (@cite{ogihara-1989})
-- ════════════════════════════════════════════════════════════════

/-!
### Connecting Attitude Accessibility to Reichenbach Frames

The attitude side (`SituationDependent.temporallyBound`) and the tense side
(`simultaneousFrame`) describe the same empirical phenomenon — the simultaneous
reading — using different formal vocabularies. The following theorems prove
their equivalence, completing the missing edge in the dependency graph.

@cite{ogihara-1989}: the bound (zero) tense variable receives the matrix event
time via lambda abstraction. The Reichenbach frame has R = P (simultaneous).
The situation-semantic formulation imposes time-equality on accessible
situations. All three descriptions collapse to the same truth condition.
-/

open Semantics.Attitudes.SituationDependent (temporallyBound)
open Core (WorldTimeIndex)

/-- Temporal binding extracts a time-equality constraint from situation
    accessibility. This is the situation-semantic formulation of "the
    embedded tense receives the matrix event time." -/
theorem temporallyBound_forces_time_eq {W Time E : Type*}
    (R : Semantics.Attitudes.SituationDependent.BAgentAccessRel W E) (agent : E)
    (s₁ s₂ : WorldTimeIndex W Time)
    (h : temporallyBound R agent s₁ s₂) :
    s₂.time = s₁.time :=
  h.2

/-- The time-equality from temporallyBound corresponds to the Reichenbach
    PRESENT relation (R = P) in the embedded frame — i.e., the simultaneous
    reading.

    This connects the attitude-side formalization (SituationDependent.temporallyBound)
    to the tense-side formalization (simultaneousFrame in IS/Tense/Basic). -/
theorem temporallyBound_gives_simultaneous {W Time E : Type*} [LinearOrder Time]
    (R : Semantics.Attitudes.SituationDependent.BAgentAccessRel W E) (agent : E)
    (s₁ s₂ : WorldTimeIndex W Time) (speechTime : Time)
    (h : temporallyBound R agent s₁ s₂) :
    let embFrame : ReichenbachFrame Time :=
      { speechTime, perspectiveTime := s₁.time,
        referenceTime := s₂.time, eventTime := s₂.time }
    embFrame.isPresent := by
  simp only [ReichenbachFrame.isPresent]
  exact temporallyBound_forces_time_eq R agent s₁ s₂ h


end Semantics.Tense.SequenceOfTense

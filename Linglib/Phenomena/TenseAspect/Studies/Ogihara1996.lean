import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Theories.Semantics.Tense.SOT.Ambiguity

/-!
# @cite{ogihara-1996}: Tense, Attitudes, and Scope
@cite{ogihara-1996} @cite{ogihara-1989}

@cite{ogihara-1996}'s theory: embedded past tense is **ambiguous**
between a genuine past reading and a zero-tense reading. Zero tense is
a bound variable that receives the matrix event time, producing the
simultaneous reading.

The substrate enum `PastReading` lives in
`Theories/Semantics/Tense/SOT/Ambiguity.lean`. This Studies file
attributes the two-reading commitment to @cite{ogihara-1996}, derives
the two predictions, and records the contrast with @cite{kratzer-1998}
(deletion, not ambiguity).

## Core Mechanisms

1. **Ambiguous past**: past morphology has two semantic values —
   genuine past (temporal precedence) vs zero tense (bound variable).
2. **Zero tense = bound variable**: receives binder time via lambda
   abstraction. The substrate primitive
   `Core.Time.Tense.zeroTense_receives_binder_time` proves the bound
   variable resolves to the binder.
3. **SOT = zero tense**: the simultaneous reading is the zero-tense
   reading.

## Key Distinction from Kratzer

- **Ogihara**: past IS semantically ambiguous (two readings).
- **Kratzer**: past is NEVER ambiguous; the simultaneous reading
  arises from morphosyntactic *deletion* of past at LF.

Both make identical predictions for the standard past-under-past data,
but they disagree about the source of the simultaneous reading:
ambiguity (Ogihara) vs deletion (Kratzer). The Phase F bridge program
will land a typed *contradiction* witness on the embedded-present
puzzle (where they actually diverge).

-/

namespace Phenomena.TenseAspect.Studies.Ogihara1996

open Core.Time.Tense
open Core.Time.Reichenbach
open Semantics.Tense
open Semantics.Tense.SOT.Ambiguity (PastReading)


-- ════════════════════════════════════════════════════════════════
-- § Ogihara's ambiguity claim (the divergence from Kratzer)
-- ════════════════════════════════════════════════════════════════

/-- @cite{ogihara-1996}'s key claim: past IS ambiguous between genuine
    past and zero tense. This is a categorical structural difference
    from @cite{kratzer-1998}'s deletion analysis. In Ogihara, the
    simultaneous reading = the zero-tense READING of past (semantic
    ambiguity); in Kratzer, it = deletion of past (morphological
    operation, no ambiguity). -/
theorem ogihara_ambiguity_vs_deletion :
    PastReading.genuinePast ≠ PastReading.zeroTense :=
  Semantics.Tense.SOT.Ambiguity.genuinePast_ne_zeroTense


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- @cite{ogihara-1996} derives the simultaneous reading via the zero
    tense reading of past: the bound variable receives `E_matrix`. The
    derivation chain is `zeroTense_receives_binder_time` (substrate) →
    `embeddedR = matrixFrame.eventTime` → `embeddedFrame.isPresent`. -/
theorem ogihara_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (g : TemporalAssignment Time) (n : ℕ) :
    let embeddedR := interpTense n (updateTemporal g n matrixFrame.eventTime)
    (embeddedFrame matrixFrame embeddedR embeddedR).isPresent := by
  simp only [zeroTense_receives_binder_time, embeddedFrame,
    ReichenbachFrame.isPresent]

/-- @cite{ogihara-1996} derives the shifted reading via the
    genuine-past reading: the past tense contributes temporal
    precedence. -/
theorem ogihara_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (hPast : embeddedR < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast]
  exact hPast


end Phenomena.TenseAspect.Studies.Ogihara1996

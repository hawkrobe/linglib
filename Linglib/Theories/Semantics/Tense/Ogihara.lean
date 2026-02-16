import Linglib.Theories.Semantics.Tense.Basic

/-!
# Ogihara (1996): Tense, Attitudes, and Scope

Ogihara's theory: embedded past is **ambiguous** between a genuine past
reading and a zero-tense reading. Zero tense is a bound variable that
receives the matrix event time, producing the simultaneous reading.

## Core Mechanisms

1. **Ambiguous past**: past morphology has two semantic values:
   - Genuine past: temporal precedence (R < eval time)
   - Zero tense: bound variable with no independent temporal content
2. **Zero tense = bound variable**: receives binder time via lambda abstraction
3. **SOT = zero tense**: the simultaneous reading is the zero-tense reading

## Key Distinction from Kratzer

- Ogihara: past IS semantically ambiguous (genuinePast vs zeroTense)
- Kratzer: past is NEVER ambiguous; simultaneous comes from deletion

Both make identical predictions for SOT phenomena, but they disagree
about the source: ambiguity (Ogihara) vs deletion (Kratzer).

## References

- Ogihara, T. (1996). *Tense, Attitudes, and Scope*. Kluwer.
- Ogihara, T. (1989). Temporal reference in English and Japanese. PhD thesis.
-/

namespace Semantics.Tense.Ogihara

open Core.Tense
open Core.Reichenbach
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Ambiguous Past
-- ════════════════════════════════════════════════════════════════

/-- Ogihara's two readings of past morphology in embedded contexts. -/
inductive OgiharaPastReading where
  /-- Genuine past: temporal precedence (R < eval time) -/
  | genuinePast
  /-- Zero tense: bound variable, no independent temporal content -/
  | zeroTense
  deriving DecidableEq, Repr, BEq

/-- Both readings are available for past-under-past in SOT languages. -/
def pastUnderPastReadings : List OgiharaPastReading :=
  [.genuinePast, .zeroTense]


-- ════════════════════════════════════════════════════════════════
-- § Zero Tense Semantics
-- ════════════════════════════════════════════════════════════════

/-- Zero tense semantics: the tense variable is bound by the attitude
    verb and receives the matrix event time. This produces R' = E_matrix
    (the simultaneous reading).

    This is exactly `zeroTense_receives_binder_time` from Core.Tense,
    applied to the attitude embedding context. -/
def zeroTenseSemantics {Time : Type*}
    (g : TemporalAssignment Time) (n : ℕ) (matrixEventTime : Time) : Time :=
  interpTense n (updateTemporal g n matrixEventTime)

/-- Zero tense semantics gives the matrix event time. -/
theorem zeroTenseSemantics_eq {Time : Type*}
    (g : TemporalAssignment Time) (n : ℕ) (matrixEventTime : Time) :
    zeroTenseSemantics g n matrixEventTime = matrixEventTime :=
  zeroTense_receives_binder_time g n matrixEventTime


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Ogihara derives the simultaneous reading via the zero tense
    reading of past: the bound variable receives E_matrix. -/
theorem ogihara_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (g : TemporalAssignment Time) (n : ℕ) :
    let embeddedR := zeroTenseSemantics g n matrixFrame.eventTime
    (embeddedFrame matrixFrame embeddedR embeddedR).isPresent := by
  simp [zeroTenseSemantics, zeroTense_receives_binder_time,
    embeddedFrame, ReichenbachFrame.isPresent]

/-- Ogihara's zero tense IS the bound-variable mechanism from Core.Tense. -/
theorem ogihara_zero_is_bound_var {Time : Type*}
    (g : TemporalAssignment Time) (n : ℕ) (binderTime : Time) :
    zeroTenseSemantics g n binderTime = binderTime :=
  zeroTense_receives_binder_time g n binderTime

/-- Ogihara derives the shifted reading via the genuine-past reading:
    the past tense contributes temporal precedence. -/
theorem ogihara_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (_hReading : OgiharaPastReading.genuinePast = .genuinePast)
    (hPast : embeddedR < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp [embeddedFrame, ReichenbachFrame.isPast]
  exact hPast

-- ════════════════════════════════════════════════════════════════
-- § Theory Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Ogihara (1996) theory identity card. -/
def Ogihara : TenseTheory where
  name := "Ogihara 1996"
  citation := "Ogihara, T. (1996). Tense, Attitudes, and Scope. Kluwer."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := true
  hasSOTDeletion := false
  simultaneousMechanism := "zero tense (ambiguous past = bound variable)"

/-- Ogihara's key claim: past IS ambiguous between genuine past and
    zero tense. This is a categorical structural difference from Kratzer.
    In Ogihara, the simultaneous reading = the zero-tense READING of past
    (semantic ambiguity); in Kratzer, it = deletion of past (morphological
    operation, no ambiguity). -/
theorem ogihara_ambiguity_vs_deletion :
    OgiharaPastReading.genuinePast ≠ OgiharaPastReading.zeroTense ∧
    Ogihara.hasZeroTense = true :=
  ⟨nofun, rfl⟩


end Semantics.Tense.Ogihara

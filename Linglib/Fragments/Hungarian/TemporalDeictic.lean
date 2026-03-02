import Linglib.Theories.Semantics.Tense.Basic

/-!
# Hungarian Temporal Deictic Adverbs
@cite{egressy-2026} @cite{zhao-2025}

Lexical entries for Hungarian temporal adverbs used as clause-size
diagnostics in @cite{egressy-2026}.

## Temporal Adverb Diagnostics

Egressy uses temporal adverbs to disambiguate embedded tense readings:
- *aznap* 'that day' — anchored to a past reference time; compatible
  with both shifted and simultaneous readings
- *előző nap* 'the day before' — forces the shifted (back-shifted) reading
  because it locates the embedded event before the matrix event
- *akkor* 'then' — perspective-shifting temporal deictic (like English
  "then", German "damals"); anchored to P ≠ S

The key diagnostic: *előző nap* is compatible with *hogy*-CP (shifted
only), confirming that the CP complement only yields the shifted reading.
But it is also compatible with the bare TP complement on its shifted
reading, while *aznap* 'that day' is compatible with the simultaneous
reading in bare TP complements.

-/

namespace Fragments.Hungarian.TemporalDeictic

open Semantics.Tense

/-- Hungarian *akkor* 'then' — perspective-shifting temporal deictic.
    Part of the cross-linguistic "then"-present incompatibility
    inventory (Zhao 2025, Tsilia, Zhao & Sharvit 2026). -/
def akkor : ThenAdverb where
  language := "Hungarian"
  form := "akkor"
  gloss := "then"
  shiftsPerspective := true

/-- Temporal adverb entry for Hungarian clause-size diagnostics.
    These are not "then"-type deictics but temporal frame adverbs
    that disambiguate embedded tense readings. -/
structure TemporalFrameAdverb where
  /-- Surface form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- Forces a shifted (back-shifted) reading? -/
  forcesShifted : Bool
  /-- Compatible with the simultaneous reading? -/
  compatSimultaneous : Bool
  deriving Repr, DecidableEq, BEq

/-- *aznap* 'that day' — compatible with both readings.
    Anchors the embedded event to the matrix event day, which is
    compatible with both shifted (event before that day) and
    simultaneous (event on that day) interpretations. -/
def aznap : TemporalFrameAdverb where
  form := "aznap"
  gloss := "that day"
  forcesShifted := false
  compatSimultaneous := true

/-- *előző nap* 'the day before' — forces shifted reading.
    Locates the embedded event before the matrix event time,
    which is only compatible with the shifted interpretation. -/
def elozo_nap : TemporalFrameAdverb where
  form := "előző nap"
  gloss := "the day before"
  forcesShifted := true
  compatSimultaneous := false

/-- All temporal frame adverbs from @cite{egressy-2026}. -/
def allFrameAdverbs : List TemporalFrameAdverb := [aznap, elozo_nap]

/-- *előző nap* forces the shifted reading. -/
theorem elozo_nap_forces_shifted :
    elozo_nap.forcesShifted = true := rfl

/-- *aznap* is compatible with both readings. -/
theorem aznap_both_readings :
    aznap.compatSimultaneous = true ∧ aznap.forcesShifted = false :=
  ⟨rfl, rfl⟩

/-- The two adverbs have different diagnostic profiles. -/
theorem diagnostic_contrast :
    aznap.compatSimultaneous ≠ elozo_nap.compatSimultaneous := by decide


end Fragments.Hungarian.TemporalDeictic

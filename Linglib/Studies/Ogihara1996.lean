import Linglib.Semantics.Tense.Basic
import Linglib.Semantics.Tense.SOT.Ambiguity
import Linglib.Data.Examples.Schema

/-!
# [ogihara-1996]: Tense, Attitudes, and Scope
[ogihara-1996] [ogihara-1989]

[ogihara-1996]'s theory: embedded past tense is **ambiguous**
between a genuine past reading and a zero-tense reading. Zero tense is
a bound variable that receives the matrix event time, producing the
simultaneous reading.

The substrate enum `PastReading` lives in
`Semantics/Tense/SOT/Ambiguity.lean`. This Studies file
attributes the two-reading commitment to [ogihara-1996], derives
the two predictions, and records the contrast with [kratzer-1998]
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

namespace Ogihara1996

open Core.Time.Tense
open Core.Time.Reichenbach
open Semantics.Tense
open Semantics.Tense.SOT.Ambiguity (PastReading)
open Data.Examples (LinguisticExample)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/Ogihara1996.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def ex2a : LinguisticExample :=
  { id := "ogihara1996_ex2a"
    source := ⟨"ogihara-1996", "(2a)"⟩
    reportedIn := none
    language := "jpan1234"
    primaryText := "Taroo-wa Hanako-ga byooki-da to it-ta."
    discourseSegments := []
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-da", "be.sick-PRES"), ("to", "COMP"), ("it-ta", "say-PAST")]
    translation := "Taro said that Hanako was sick [at that time]."
    context := "Past matrix + PRESENT embedded → simultaneous reading. In non-SOT Japanese, the embedded clause uses present (`-da`) to express simultaneity with the saying time; the embedded clause's tense is interpreted relative to speech time, so PRESENT here is anchored to the saying time via attitude-context shift, not to speech time."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (Hanako sick at saying time)", .acceptable), ("shifted (Hanako sick before saying)", .ungrammatical)]
    paperFeatures := []
    comment := "Ogihara 1996 ex (2a), Chapter 1 §1.2 p. 11. Half of the minimal pair (2a)/(2b) — the embedded PRESENT form. Together with (2b) below, motivates Ogihara's analysis: embedded tense in Japanese is absolute, so PRESENT delivers simultaneity (via attitude shift) and PAST delivers strict backward shift."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "ogihara1996_ex2b"
    source := ⟨"ogihara-1996", "(2b)"⟩
    reportedIn := none
    language := "jpan1234"
    primaryText := "Taroo-wa Hanako-ga byookidat-ta to it-ta."
    discourseSegments := []
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byookidat-ta", "be.sick-PAST"), ("to", "COMP"), ("it-ta", "say-PAST")]
    translation := "Taro said that Hanako had been sick."
    context := "Past matrix + PAST embedded → ONLY shifted reading. Hanako's sickness strictly precedes the saying. No simultaneous reading is available — sharply diagnostic of non-SOT Japanese vs SOT English."
    judgment := .acceptable
    alternatives := []
    readings := [("shifted (Hanako sick before saying)", .acceptable), ("simultaneous (Hanako sick at saying time)", .ungrammatical)]
    paperFeatures := []
    comment := "Ogihara 1996 ex (2b), Chapter 1 §1.2 p. 11. The other half of the minimal pair. With English-style SOT, the embedded past should admit a simultaneous reading; its unavailability here is Ogihara's main empirical hook."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex19d : LinguisticExample :=
  { id := "ogihara1996_ex19d"
    source := ⟨"ogihara-1996", "(19d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said that Mary had been reading books yesterday."
    discourseSegments := []
    glossedTokens := []
    translation := "He said that Mary had been reading books yesterday."
    context := "English past perfect under past matrix. The adverbial `yesterday` denotes a definite past interval and restricts the embedded event's temporal location — solid evidence that the perfect can be used as a preterit."
    judgment := .acceptable
    alternatives := []
    readings := [("Mary's reading at yesterday (definite past)", .acceptable)]
    paperFeatures := []
    comment := "Ogihara 1996 ex (19d), Chapter 1 §1.4 p. 12. Part of the (18a-d)/(19a-d) discussion arguing the perfect can be a preterit. The adverbial-licensing argument: definite-past adverbials like `yesterday` co-occur with the perfect, showing the perfect doesn't always require an open interval up to reference time."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex2a, ex2b, ex19d]

end Examples
-- END GENERATED EXAMPLES


-- ════════════════════════════════════════════════════════════════
-- § Ogihara's ambiguity claim (the divergence from Kratzer)
-- ════════════════════════════════════════════════════════════════

/-- [ogihara-1996]'s key claim: past IS ambiguous between genuine
    past and zero tense. This is a categorical structural difference
    from [kratzer-1998]'s deletion analysis. In Ogihara, the
    simultaneous reading = the zero-tense READING of past (semantic
    ambiguity); in Kratzer, it = deletion of past (morphological
    operation, no ambiguity). -/
theorem ogihara_ambiguity_vs_deletion :
    PastReading.genuinePast ≠ PastReading.zeroTense :=
  Semantics.Tense.SOT.Ambiguity.genuinePast_ne_zeroTense


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- [ogihara-1996] derives the simultaneous reading via the zero
    tense reading of past: the bound variable receives `E_matrix`. The
    derivation chain is `zeroTense_receives_binder_time` (substrate) →
    `embeddedR = matrixFrame.eventTime` → `embeddedFrame.isPresent`. -/
theorem ogihara_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (g : TemporalAssignment Time) (n : ℕ) :
    let embeddedR := interpTense n (updateTemporal g n matrixFrame.eventTime)
    (embeddedFrame matrixFrame embeddedR embeddedR).isPresent := by
  simp only [zeroTense_receives_binder_time, embeddedFrame,
    ReichenbachFrame.isPresent]

/-- [ogihara-1996] derives the shifted reading via the
    genuine-past reading: the past tense contributes temporal
    precedence. -/
theorem ogihara_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (hPast : embeddedR < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp only [embeddedFrame, ReichenbachFrame.isPast]
  exact hPast


-- ════════════════════════════════════════════════════════════════
-- § Empirical Data: Japanese non-SOT + Pluperfect (Ogihara 1996 Ch. 1)
-- ════════════════════════════════════════════════════════════════

/-! Reichenbach data frames for the Ogihara diagnostics that the schema
    cleanly admits. Verified against the book text:
    - **(2b)** `Taroo-wa Hanako-ga byookidat-ta to it-ta` (PAST matrix +
      PAST embedded) → ONLY shifted (`embeddedByookiDatta`).
    - **(19d)** "He said that Mary had been reading books yesterday"
      → past perfect with definite-past adverbial (`pluperfectShifted`).

    **Schema-gap caveat: ex (2a) is intentionally not Lean-encoded.**
    Ogihara ex (2a) `Taroo-wa Hanako-ga byooki-da to it-ta` (PAST matrix
    + PRESENT embedded) has a simultaneous reading: Hanako is sick at
    Taro's saying time. The `ReichenbachFrame` schema cannot model this
    faithfully — the embedded morphology says PRESENT (R = S), but the
    simultaneous interpretation places the event at matrix E (≠ S).
    A single (R, E) pair cannot simultaneously encode the morphological
    tense AND the divergent event location. This is a general gap that
    also bites counterfactual past, fake past, historical present, and
    FID; it is not specific to Ogihara. The JSON record
    `Examples.ex2a` captures the empirical pair (sentence + readings)
    without committing to a Reichenbach analysis.

    The pluperfect frame is built via `embeddedFrame` against the
    local `matrixItta` (per CLAUDE.md "Theory-hub denotation as
    study-file constraint" — `matrixItta`'s S/P/R/E = (0, 0, -2, -2)
    matches the generic "X said Y" matrix shape, so the (19d)
    "He said …" construction reuses it). The Japanese matrix is
    root-clause; per Ogihara's absolute-tense analysis the embedded
    (2b) frame keeps P = S = 0. -/

/-- Japanese matrix frame `Taroo-wa ... to it-ta` (Taro said ...).
    Past tense, perfective. S = P = 0, R = E = -2. -/
def matrixItta : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2

/-- Ogihara ex (2b) embedded `Hanako-ga byookidat-ta` (Hanako had been
    sick) — PAST under PAST, ONLY the shifted reading. In non-SOT
    Japanese, embedded past is absolute (R < S, not R < matrix E).
    The unavailability of the simultaneous reading is Ogihara's
    cornerstone diagnostic.

    Encoded as a standalone root-style frame (P = S = 0): per Ogihara
    Ch. 1 (p. 12), Japanese is an "absolute tense" language; the
    embedded clause does NOT shift its perspective time — that's
    precisely the empirical content of "absolute, not relative". -/
def embeddedByookiDatta : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- Ogihara ex (19d) "He said that Mary had been reading books yesterday."
    English past perfect under past matrix. R < P (past) + E < R (perfect):
    the reading event precedes the reference time (within "yesterday"),
    which precedes the saying. Built via `embeddedFrame` against
    `matrixItta` (S/P/R/E = (0,0,-2,-2) — the generic "X said Y" matrix
    shape, reusable for the (19d) English example). -/
def pluperfectShifted : ReichenbachFrame ℤ :=
  embeddedFrame matrixItta (-4) (-5)


-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Verifications
-- ════════════════════════════════════════════════════════════════

/-- Japanese non-SOT: embedded perspective stays at speech time
    (the diagnostic content of "absolute"). -/
theorem japanese_absolute_perspective :
    embeddedByookiDatta.perspectiveTime = embeddedByookiDatta.speechTime := rfl

/-- Pluperfect: E < R (perfect aspect: event before reference). -/
theorem pluperfect_is_perfect : pluperfectShifted.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, pluperfectShifted, embeddedFrame,
    matrixItta]; omega

/-- Pluperfect: R < P (past tense relative to embedded perspective). -/
theorem pluperfect_is_past : pluperfectShifted.isPast := by
  simp only [ReichenbachFrame.isPast, pluperfectShifted, embeddedFrame,
    matrixItta]; omega


end Ogihara1996

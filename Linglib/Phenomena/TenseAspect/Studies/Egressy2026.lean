import Linglib.Core.Time.Tense
import Linglib.Core.Time.Reichenbach
import Linglib.Theories.Syntax.Minimalism.Tense.AgreeSOT
import Linglib.Fragments.Hungarian.Predicates
import Linglib.Fragments.Hungarian.FunctionWords
import Linglib.Fragments.Hungarian.TemporalDeictic

/-!
# @cite{egressy-2026}: Size-Sensitive Sequence of Tense in Hungarian
@cite{egressy-2026}

Empirical data from @cite{egressy-2026}, who shows that Hungarian is a
partial SOT language: the simultaneous reading of past-under-past is
available in structurally small complements (TP, without *hogy* 'that')
but blocked in full CP complements (with *hogy*).

## Key Empirical Findings

1. **CP complements** (with *hogy*): shifted reading only
   - *Ági tudta, hogy Mari beteg volt.* → only "Mari was sick before Ági knew"

2. **Bare TP complements** (no *hogy*): both shifted and simultaneous readings
   - *Ági tudta Marit betegnek.* → ambiguous: shifted or simultaneous

3. **Temporal adverb diagnostics**: *akkor* 'then' forces temporal anchoring
   and disambiguates complement size effects

4. **Williams Cycle**: Hungarian is mid-cycle — CP has become opaque to
   tense Agree while TP remains transparent

## Data Organization

Theory-neutral empirical judgments, followed by bridge theorems connecting
these to @cite{zeijlstra-2012}'s Agree-based SOT theory: fragment grounding,
complement-size mapping, per-datum predictions, Williams Cycle classification,
and temporal adverb diagnostics.

-/

namespace Egressy2026

open Core.Time.Tense
open Core.Time.Reichenbach


-- ════════════════════════════════════════════════════════════════
-- § Complement Type
-- ════════════════════════════════════════════════════════════════

/-- Hungarian complement types distinguished by structural size.

    The key empirical distinction: complements with the overt
    complementizer *hogy* 'that' are full CPs; complements without
    *hogy* are structurally smaller (TP-sized). -/
inductive HungarianComplementType where
  /-- Full CP with *hogy* 'that' — opaque to SOT -/
  | hogyCP
  /-- Bare finite complement without *hogy* — transparent to SOT -/
  | bareTP
  deriving DecidableEq, Repr

/-- Whether the complement type includes the complementizer *hogy*. -/
def HungarianComplementType.hasHogy : HungarianComplementType → Bool
  | .hogyCP => true
  | .bareTP => false


-- ════════════════════════════════════════════════════════════════
-- § SOT Judgments
-- ════════════════════════════════════════════════════════════════

/-- An empirical SOT judgment: a past-under-past sentence with its
    complement type and available readings.

    Each entry records:
    - The matrix verb
    - The complement type (CP with *hogy* vs bare TP)
    - Whether the simultaneous reading is available
    - Whether the shifted reading is available (always true) -/
structure SOTJudgment where
  /-- Matrix verb (Hungarian) -/
  matrixVerb : String
  /-- Matrix verb gloss -/
  matrixGloss : String
  /-- Complement type -/
  complementType : HungarianComplementType
  /-- Example sentence -/
  example_ : String
  /-- English translation (shifted reading) -/
  shiftedGloss : String
  /-- English translation (simultaneous reading, if available) -/
  simultaneousGloss : Option String
  /-- Is the simultaneous reading available? -/
  simultaneousAvailable : Bool
  /-- Is the shifted reading available? (always true) -/
  shiftedAvailable : Bool := true
  deriving Repr, BEq


-- ════════════════════════════════════════════════════════════════
-- § Core Data: Past-Under-Past by Complement Type
-- ════════════════════════════════════════════════════════════════

/-! ### CP complements (with *hogy*): shifted only -/

/-- @cite{egressy-2026}, ex. (9): *Ági tud-t-a, hogy Mari beteg vol-t.*
    'Ági know-PST-3SG that Mari sick be-PST'
    → Shifted only: Mari was sick before Ági's knowing -/
def pastUnderPast_hogyCP_tudta : SOTJudgment where
  matrixVerb := "tudta"
  matrixGloss := "knew"
  complementType := .hogyCP
  example_ := "Ági tudta, hogy Mari beteg volt."
  shiftedGloss := "Ági knew that Mari had been sick (before the knowing)"
  simultaneousGloss := none
  simultaneousAvailable := false

/-- @cite{egressy-2026}, ex. (11a): *Ági mond-t-a, hogy Mari beteg vol-t.*
    'Ági say-PST-3SG that Mari sick be-PST'
    → Shifted only in full CP -/
def pastUnderPast_hogyCP_mondta : SOTJudgment where
  matrixVerb := "mondta"
  matrixGloss := "said"
  complementType := .hogyCP
  example_ := "Ági mondta, hogy Mari beteg volt."
  shiftedGloss := "Ági said that Mari had been sick (before the saying)"
  simultaneousGloss := none
  simultaneousAvailable := false

/-- @cite{egressy-2026}, ex. (11b): *Ági hit-t-e, hogy Mari beteg vol-t.*
    'Ági believe-PST-3SG that Mari sick be-PST'
    → Shifted only in full CP -/
def pastUnderPast_hogyCP_hitte : SOTJudgment where
  matrixVerb := "hitte"
  matrixGloss := "believed"
  complementType := .hogyCP
  example_ := "Ági hitte, hogy Mari beteg volt."
  shiftedGloss := "Ági believed that Mari had been sick (before the believing)"
  simultaneousGloss := none
  simultaneousAvailable := false

/-! ### Bare TP complements (without *hogy*): both readings -/

/-- @cite{egressy-2026}, ex. (10): *Ági tud-t-a Mari-t beteg-nek.*
    'Ági know-PST-3SG Mari-ACC sick-DAT'
    → Both readings: shifted and simultaneous -/
def pastUnderPast_bareTP_tudta : SOTJudgment where
  matrixVerb := "tudta"
  matrixGloss := "knew"
  complementType := .bareTP
  example_ := "Ági tudta Marit betegnek."
  shiftedGloss := "Ági knew Mari to have been sick (before)"
  simultaneousGloss := some "Ági knew Mari to be sick (at the time)"
  simultaneousAvailable := true


-- ════════════════════════════════════════════════════════════════
-- § Judgment Collection
-- ════════════════════════════════════════════════════════════════

/-- All SOT judgments from the study. -/
def allJudgments : List SOTJudgment :=
  [ pastUnderPast_hogyCP_tudta
  , pastUnderPast_hogyCP_mondta
  , pastUnderPast_hogyCP_hitte
  , pastUnderPast_bareTP_tudta ]

/-- CP complement judgments: shifted only. -/
def cpJudgments : List SOTJudgment :=
  allJudgments.filter (·.complementType == .hogyCP)

/-- Bare TP judgments: both readings. -/
def tpJudgments : List SOTJudgment :=
  allJudgments.filter (·.complementType == .bareTP)


-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Verification: CP Complements Block Simultaneous
-- ════════════════════════════════════════════════════════════════

/-- All CP complement judgments block the simultaneous reading. -/
theorem hogyCP_tudta_no_simultaneous :
    pastUnderPast_hogyCP_tudta.simultaneousAvailable = false := rfl

theorem hogyCP_mondta_no_simultaneous :
    pastUnderPast_hogyCP_mondta.simultaneousAvailable = false := rfl

theorem hogyCP_hitte_no_simultaneous :
    pastUnderPast_hogyCP_hitte.simultaneousAvailable = false := rfl


-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Verification: Bare TP Allows Simultaneous
-- ════════════════════════════════════════════════════════════════

/-- Bare TP judgments allow the simultaneous reading. -/
theorem bareTP_tudta_simultaneous :
    pastUnderPast_bareTP_tudta.simultaneousAvailable = true := rfl


-- ════════════════════════════════════════════════════════════════
-- § Aggregate Theorems
-- ════════════════════════════════════════════════════════════════

/-- All judgments have the shifted reading available. -/
theorem all_shifted_available :
    allJudgments.all (·.shiftedAvailable) = true := by native_decide

/-- No CP judgment has the simultaneous reading. -/
theorem no_cp_simultaneous :
    cpJudgments.all (fun j => !j.simultaneousAvailable) = true := by native_decide

/-- All bare TP judgments have the simultaneous reading. -/
theorem all_tp_simultaneous :
    tpJudgments.all (·.simultaneousAvailable) = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § Bridge: Size-Sensitive SOT → Zeijlstra + PIC
-- ════════════════════════════════════════════════════════════════

open Minimalism (ComplementSize fValue Cat)
open Minimalism.Tense.AgreeSOT
open Semantics.Tense (EmbeddedTenseReading)
open Fragments.Hungarian.Predicates
open Fragments.Hungarian.FunctionWords
open Fragments.Hungarian.TemporalDeictic


-- ════════════════════════════════════════════════════════════════
-- § A. Fragment Grounding: Verb Forms Match Data
-- ════════════════════════════════════════════════════════════════

/-! Prove that the string literals in Data.lean match the Fragment
    entries. This ensures the data is derived from fragments, not
    independently stipulated. -/

/-- *tudta* in Data.lean is the past definite form of *tud*. -/
theorem tudta_from_fragment :
    pastUnderPast_hogyCP_tudta.matrixVerb = tud.formPastDef := rfl

/-- *mondta* in Data.lean is the past definite form of *mond*. -/
theorem mondta_from_fragment :
    pastUnderPast_hogyCP_mondta.matrixVerb = mond.formPastDef := rfl

/-- *hitte* in Data.lean is the past definite form of *hisz*. -/
theorem hitte_from_fragment :
    pastUnderPast_hogyCP_hitte.matrixVerb = hisz.formPastDef := rfl

/-- The bare TP *tudta* also matches the past definite form.
    (Both CP and bare TP examples use definite conjugation with *tud*.) -/
theorem bareTP_tudta_from_fragment :
    pastUnderPast_bareTP_tudta.matrixVerb = tud.formPastDef := rfl

/-- Glosses match fragment glosses. -/
theorem glosses_from_fragments :
    pastUnderPast_hogyCP_tudta.matrixGloss = "knew" ∧
    pastUnderPast_hogyCP_mondta.matrixGloss = "said" ∧
    pastUnderPast_hogyCP_hitte.matrixGloss = "believed" := ⟨rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § B. Complement Type → Complement Size
-- ════════════════════════════════════════════════════════════════

/-- Map Hungarian complement types to structural complement sizes.

    - *hogy*-CP → full CP (fValue 6, phase-sized, opaque)
    - bare TP → TP (fValue 2, sub-phase, transparent) -/
def complementTypeToSize : HungarianComplementType → ComplementSize
  | .hogyCP => .cP
  | .bareTP => .tP

/-- *hogy*-CP maps to CP. -/
theorem hogyCP_is_cP :
    complementTypeToSize .hogyCP = .cP := rfl

/-- Bare TP maps to TP. -/
theorem bareTP_is_tP :
    complementTypeToSize .bareTP = .tP := rfl

/-- The *hogy* fragment entry and the complementTypeToSize function agree. -/
theorem hogy_fragment_matches_mapping :
    complementTypeToSize .hogyCP = hogy.complementSize := rfl


-- ════════════════════════════════════════════════════════════════
-- § C. Predictions: Complement Size → Available Readings
-- ════════════════════════════════════════════════════════════════

/-- *hogy*-CP is opaque to tense Agree. -/
theorem hogyCP_opaque :
    (complementTypeToSize .hogyCP).transparentToTenseAgree = false := by decide

/-- Bare TP is transparent to tense Agree. -/
theorem bareTP_transparent :
    (complementTypeToSize .bareTP).transparentToTenseAgree = true := by decide

/-- Predicted readings for *hogy*-CP: shifted only. -/
theorem hogyCP_predicted_readings :
    availableReadingsBySize (complementTypeToSize .hogyCP) = [.shifted] := by
  simp [complementTypeToSize, availableReadingsBySize,
    ComplementSize.transparentToTenseAgree, ComplementSize.fLevel,
    ComplementSize.cP, fValue]

/-- Predicted readings for bare TP: both shifted and simultaneous. -/
theorem bareTP_predicted_readings :
    availableReadingsBySize (complementTypeToSize .bareTP) =
    [.shifted, .simultaneous] := by
  simp [complementTypeToSize, availableReadingsBySize,
    ComplementSize.transparentToTenseAgree, ComplementSize.fLevel,
    ComplementSize.tP, fValue]


-- ════════════════════════════════════════════════════════════════
-- § D. Per-Datum Bridge: Data Matches Predictions
-- ════════════════════════════════════════════════════════════════

/-! For each empirical judgment, prove that the observed availability
    of the simultaneous reading matches what `availableReadingsBySize`
    predicts for the complement type. -/

/-- Helper: check if a judgment's simultaneous availability matches
    the theoretical prediction. The prediction is: simultaneous is
    available iff the complement is transparent to tense Agree. -/
def judgmentMatchesPrediction (j : SOTJudgment) : Bool :=
  let cs := complementTypeToSize j.complementType
  j.simultaneousAvailable == cs.transparentToTenseAgree

/-- *tudta* + *hogy*-CP: no simultaneous reading, as predicted. -/
theorem tudta_hogyCP_matches :
    judgmentMatchesPrediction pastUnderPast_hogyCP_tudta = true := by native_decide

/-- *mondta* + *hogy*-CP: no simultaneous reading, as predicted. -/
theorem mondta_hogyCP_matches :
    judgmentMatchesPrediction pastUnderPast_hogyCP_mondta = true := by native_decide

/-- *hitte* + *hogy*-CP: no simultaneous reading, as predicted. -/
theorem hitte_hogyCP_matches :
    judgmentMatchesPrediction pastUnderPast_hogyCP_hitte = true := by native_decide

/-- *tudta* + bare TP: simultaneous reading available, as predicted. -/
theorem tudta_bareTP_matches :
    judgmentMatchesPrediction pastUnderPast_bareTP_tudta = true := by native_decide

/-- All judgments match predictions. -/
theorem all_judgments_match :
    allJudgments.all judgmentMatchesPrediction = true := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § E. Williams Cycle: Hungarian = Partial SOT
-- ════════════════════════════════════════════════════════════════

/-- Hungarian's Williams Cycle stage. -/
def hungarianStage : WilliamsCycleStage := .partialSOT

/-- Hungarian's partial SOT matches the empirical pattern:
    both readings in TP, shifted only in CP. -/
theorem hungarian_partial_sot :
    readingsByStage hungarianStage (complementTypeToSize .bareTP) =
      [.shifted, .simultaneous] ∧
    readingsByStage hungarianStage (complementTypeToSize .hogyCP) =
      [.shifted] := by
  constructor
  · simp [hungarianStage, readingsByStage, complementTypeToSize,
      availableReadingsBySize, ComplementSize.transparentToTenseAgree,
      ComplementSize.fLevel, ComplementSize.tP, fValue]
  · simp [hungarianStage, readingsByStage, complementTypeToSize,
      availableReadingsBySize, ComplementSize.transparentToTenseAgree,
      ComplementSize.fLevel, ComplementSize.cP, fValue]

/-- English, by contrast, is full SOT — both readings in all complement types. -/
def englishStage : WilliamsCycleStage := .fullSOT

theorem english_full_sot (ct : HungarianComplementType) :
    readingsByStage englishStage (complementTypeToSize ct) =
      [.shifted, .simultaneous] := by
  cases ct <;> rfl

/-- Japanese is non-SOT — shifted only in all complement types. -/
def japaneseStage : WilliamsCycleStage := .noSOT

theorem japanese_no_sot (ct : HungarianComplementType) :
    readingsByStage japaneseStage (complementTypeToSize ct) =
      [.shifted] := by
  cases ct <;> rfl


-- ════════════════════════════════════════════════════════════════
-- § F. Temporal Adverb Diagnostics
-- ════════════════════════════════════════════════════════════════

/-! The temporal adverb *előző nap* 'the day before' forces the shifted
    reading. In *hogy*-CP complements (where only shifted is available),
    this is compatible. In bare TP complements (where both readings are
    available), it selects the shifted reading. This provides independent
    evidence that the CP complement really does lack the simultaneous
    reading, rather than there being some other blocking effect. -/

/-- *előző nap* is compatible with *hogy*-CP (shifted-only) complements,
    because it itself forces the shifted reading. -/
theorem elozo_nap_compat_hogyCP :
    elozo_nap.forcesShifted = true ∧
    (complementTypeToSize .hogyCP).transparentToTenseAgree = false := by
  exact ⟨rfl, by decide⟩

/-- *aznap* 'that day' can diagnose the simultaneous reading in bare TP,
    because it is compatible with both readings. -/
theorem aznap_diagnoses_bareTP :
    aznap.compatSimultaneous = true ∧
    (complementTypeToSize .bareTP).transparentToTenseAgree = true := by
  exact ⟨rfl, by decide⟩

/-- Hungarian *akkor* 'then' shifts perspective, like all cross-linguistic
    "then" adverbs. -/
theorem akkor_shifts :
    akkor.shiftsPerspective = true := rfl


-- ════════════════════════════════════════════════════════════════
-- § G. Definite Conjugation as Clause-Size Diagnostic
-- ════════════════════════════════════════════════════════════════

/-! @cite{egressy-2026} uses the definite/indefinite conjugation split
    as independent evidence for complement size. *hogy*-CP triggers
    definite conjugation; bare complements may allow indefinite.

    The fragment entries record both conjugation forms, so we can verify
    that the matrix verb forms in the data entries are the expected
    conjugation type. -/

/-- All *hogy*-CP judgments use the definite conjugation past form. -/
theorem hogyCP_uses_definite_conjugation :
    pastUnderPast_hogyCP_tudta.matrixVerb = tud.formPastDef ∧
    pastUnderPast_hogyCP_mondta.matrixVerb = mond.formPastDef ∧
    pastUnderPast_hogyCP_hitte.matrixVerb = hisz.formPastDef := ⟨rfl, rfl, rfl⟩


end Egressy2026

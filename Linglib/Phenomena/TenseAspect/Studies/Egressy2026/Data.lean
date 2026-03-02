import Linglib.Core.Temporal.Tense
import Linglib.Core.Temporal.Reichenbach

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

Theory-neutral empirical judgments only. Bridge theorems connecting
these to Zeijlstra's Agree-based SOT are in `Bridge.lean`.

-/

namespace Phenomena.TenseAspect.Studies.Egressy2026

open Core.Tense
open Core.Reichenbach


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
  deriving DecidableEq, Repr, BEq

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


end Phenomena.TenseAspect.Studies.Egressy2026

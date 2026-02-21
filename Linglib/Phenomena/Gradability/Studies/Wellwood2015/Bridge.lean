import Linglib.Phenomena.Gradability.Studies.Wellwood2015.Data
import Linglib.Theories.Semantics.Lexical.Measurement

/-!
# Wellwood (2015): Theory–Data Bridge

@cite{wellwood-2015}

Per-datum verification that `Measurement.lean`'s mereological status
classification predicts the empirical felicity patterns in `Data.lean`.

The bridge function `lexCatToStatus` maps each `LexCat` to a
`MereologicalStatus` using the theory's cross-categorial bridges
(`telicityToStatus`, `numberToStatus`, `gradableToStatus`,
`nonGradableToStatus`). The prediction: `.cumulative` categories
are felicitous with `much`, `.quantized` categories are not.

The grammar shift bridges (§4) ground Wellwood's §5 in the existing
`AspectualProfile.telicize` / `.atelicize` operations from
`Lexical.Verb.Aspect`, showing that grammatical shifts that change
telicity also change measurement status.

## References

- Wellwood, A. (2015). On the semantics of comparison across categories.
  Linguistics and Philosophy 38(1): 67-101.
-/

namespace Phenomena.Gradability.Wellwood2015.Bridge

open Phenomena.Gradability.Wellwood2015
open Semantics.Lexical.Measurement
open Semantics.Lexical.Verb.Aspect (AspectualProfile)

-- ════════════════════════════════════════════════════
-- § 1. Theory Prediction
-- ════════════════════════════════════════════════════

/-- Map `LexCat` to `MereologicalStatus` using the theory's bridges. -/
def lexCatToStatus : LexCat → MereologicalStatus
  | .massNoun       => numberToStatus .mass
  | .countNoun      => numberToStatus .sg
  | .atelicVP       => telicityToStatus .atelic
  | .telicVP        => telicityToStatus .telic
  | .gradableAdj    => gradableToStatus
  | .nonGradableAdj => nonGradableToStatus

/-- The theory predicts: cumulative → felicitous with `much`. -/
def statusPredictsFelicitous : MereologicalStatus → Bool
  | .cumulative => true
  | .quantized  => false

-- ════════════════════════════════════════════════════
-- § 2. Per-Datum Felicity Bridges
-- ════════════════════════════════════════════════════

/-- Mass nouns: theory predicts cumulative → felicitous. ✓ -/
theorem massNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .massNoun) =
      massNounDatum.felicitousWithMuch := rfl

/-- Count nouns: theory predicts quantized → not felicitous. ✓ -/
theorem countNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .countNoun) =
      countNounDatum.felicitousWithMuch := rfl

/-- Atelic VPs: theory predicts cumulative → felicitous. ✓ -/
theorem atelicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .atelicVP) =
      atelicVPDatum.felicitousWithMuch := rfl

/-- Telic VPs: theory predicts quantized → not felicitous. ✓ -/
theorem telicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .telicVP) =
      telicVPDatum.felicitousWithMuch := rfl

/-- Gradable adjectives: theory predicts cumulative → felicitous. ✓ -/
theorem gradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .gradableAdj) =
      gradableAdjDatum.felicitousWithMuch := rfl

/-- Non-gradable adjectives: theory predicts quantized → not felicitous. ✓ -/
theorem nonGradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .nonGradableAdj) =
      nonGradableAdjDatum.felicitousWithMuch := rfl

-- ════════════════════════════════════════════════════
-- § 3. Cross-Categorial Parallel Bridge
-- ════════════════════════════════════════════════════

/-- Mass nouns and atelic VPs share the same mereological status. -/
theorem massNoun_atelicVP_same_status :
    lexCatToStatus .massNoun = lexCatToStatus .atelicVP := rfl

/-- Count nouns and telic VPs share the same mereological status. -/
theorem countNoun_telicVP_same_status :
    lexCatToStatus .countNoun = lexCatToStatus .telicVP := rfl

/-- Gradable adjectives share status with mass nouns and atelic VPs. -/
theorem gradableAdj_patterns_with_cum :
    lexCatToStatus .gradableAdj = lexCatToStatus .massNoun := rfl

/-- Non-gradable adjectives share status with count nouns and telic VPs. -/
theorem nonGradableAdj_patterns_with_qua :
    lexCatToStatus .nonGradableAdj = lexCatToStatus .countNoun := rfl

-- ════════════════════════════════════════════════════
-- § 4. Grammar Shift Bridges
-- ════════════════════════════════════════════════════

/-- "ran in the park" → "ran to the park" (Wellwood ex. 105):
    telicization via `AspectualProfile.telicize` shifts cumulative → quantized.
    Extensive dimensions (DURATION, DISTANCE) → blocked; only NUMBER available.

    This grounds the grammar shift datum in the existing aspectual shift
    infrastructure rather than asserting it by fiat: `telicize_shifts_status`
    proves that the shift follows from the telicity change. -/
theorem run_shift_via_telicize :
    let p : AspectualProfile := Semantics.Lexical.Verb.Aspect.activityProfile
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  telicize_shifts_status _ rfl

/-- "was building the house" → "built the house" (progressive removal):
    atelicization via `AspectualProfile.atelicize` shifts quantized → cumulative.
    Extensive dimensions restored. -/
theorem build_shift_via_atelicize :
    let p : AspectualProfile := Semantics.Lexical.Verb.Aspect.accomplishmentProfile
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative :=
  atelicize_shifts_status _ rfl

/-- rock → rocks: mass (cumulative) → count (quantized).
    Number morphology restricts measurement to NUMBER. -/
theorem rock_shift_status :
    lexCatToStatus .massNoun = .cumulative ∧
    lexCatToStatus .countNoun = .quantized := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Boundedness Bridge
-- ════════════════════════════════════════════════════

/-- All cumulative categories map to open scales; all quantized categories
    map to closed scales. This connects the per-datum felicity predictions
    to Kennedy's (2007) scale structure. -/
theorem massNoun_open_scale :
    (lexCatToStatus .massNoun).toBoundedness = .open_ := rfl

theorem countNoun_closed_scale :
    (lexCatToStatus .countNoun).toBoundedness = .closed := rfl

theorem atelicVP_open_scale :
    (lexCatToStatus .atelicVP).toBoundedness = .open_ := rfl

theorem telicVP_closed_scale :
    (lexCatToStatus .telicVP).toBoundedness = .closed := rfl

end Phenomena.Gradability.Wellwood2015.Bridge

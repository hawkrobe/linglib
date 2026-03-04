import Linglib.Phenomena.FillerGap.TobaBatak
import Linglib.Theories.Syntax.Minimalism.Core.Position

/-!
# Minimalism Bridge: Toba Batak Extraction Restriction @cite{erlewine-2018}
@cite{elkins-imanishi-coon-2026}

Connects the empirical extraction data from Toba Batak to the
Minimalist analysis in @cite{erlewine-2018}.

## The Analysis (@cite{erlewine-2018}, §3–4)

The extraction restriction follows from the interaction of probing
and nominal licensing:

1. **Predicate fronting** (§4.2): C bears `[PROBE:FOC]`, which attracts
   the closest `[+FOC]` constituent — normally the vP — to Spec,CP,
   deriving V-initial word order. The subject/pivot is stranded in
   Spec,TP after vP fronts.

2. **Nominal licensing** (§4): T bears `[PROBE:D]`, which Case-licenses
   the subject DP in Spec,TP. If a non-subject DP were attracted to
   Spec,CP by `[PROBE:FOC]`, it would end up in a position with no
   available Case licensor — the derivation crashes. Therefore only the
   pivot (already Case-licensed by T) can be Ā-extracted.

3. **Non-DP extraction is unrestricted** (§4.3): Since the restriction
   is about nominal licensing, non-DP constituents (adverbs, PPs) can
   freely front to Spec,CP regardless of voice.

The descriptive generalization is: extraction of a DP argument is
grammatical iff it is the pivot for the given voice.

## Connection to Mam

Both TB and Mam involve successive-cyclic movement leaving
morphological traces at clause boundaries. The shared abstraction
is `CyclicChain` from Position.lean:

- **Mam**: Each intermediate Voice⁰ Agrees [+oblique], spelling out
  as =(y)a'. The chain entries correspond to feature-valuation events.
- **TB**: Each intermediate C⁰ shows extraction voice morphology,
  reflecting the passage of the wh-element through Spec,CP.

-/

namespace Phenomena.FillerGap.Studies.Erlewine2018

open Fragments.TobaBatak

-- ============================================================================
-- § 1: Prediction Function
-- ============================================================================

/-- Predict whether extraction is grammatical from voice + extractee.

    The nominal licensing analysis predicts:
    - DP arguments: extraction is grammatical iff the DP is the pivot,
      because only the pivot is Case-licensed (by T's [PROBE:D] in
      Spec,TP) before Ā-extraction (§2–4).
    - Non-DP adjuncts: always grammatical, because adjuncts don't need
      Case licensing (§4.3). -/
def predictExtraction (voice : Fragments.TobaBatak.Voice) (extractee : Interfaces.Extractee) :
    ExtractionJudgment :=
  match extractee with
  | .adjunct => .grammatical
  | .dpArg role =>
    if role == voice.pivotRole then .grammatical else .ungrammatical

-- ============================================================================
-- § 2: Per-Datum Bridge Theorems
-- ============================================================================

/-- AV + agent (pivot): Case-licensed in Spec,TP → extractable. -/
theorem bridge_av_agent :
    predictExtraction .av (.dpArg .agent) = .grammatical ∧
    avAgentExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

/-- AV + patient (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_av_patient :
    predictExtraction .av (.dpArg .patient) = .ungrammatical ∧
    avPatientExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

/-- AV + oblique (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_av_oblique :
    predictExtraction .av (.dpArg .oblique) = .ungrammatical ∧
    avObliqueExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

/-- OV + patient (pivot): Case-licensed in Spec,TP → extractable. -/
theorem bridge_ov_patient :
    predictExtraction .ov (.dpArg .patient) = .grammatical ∧
    ovPatientExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

/-- OV + agent (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_ov_agent :
    predictExtraction .ov (.dpArg .agent) = .ungrammatical ∧
    ovAgentExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

/-- OV + oblique (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_ov_oblique :
    predictExtraction .ov (.dpArg .oblique) = .ungrammatical ∧
    ovObliqueExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

/-- AV + adjunct: no Case needed → freely extractable (§4.3). -/
theorem bridge_av_adjunct :
    predictExtraction .av .adjunct = .grammatical ∧
    avAdjunctExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

/-- OV + adjunct: no Case needed → freely extractable (§4.3). -/
theorem bridge_ov_adjunct :
    predictExtraction .ov .adjunct = .grammatical ∧
    ovAdjunctExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Completeness
-- ============================================================================

/-- The structural analysis correctly predicts every monoclausal datum. -/
theorem all_predictions_match :
    extractionData.all (λ d =>
      predictExtraction d.voice d.extracted == d.judgment) = true := by
  native_decide

/-- For DP arguments, the prediction function agrees with extractsPivot:
    extraction is grammatical iff the extracted element is the voice-
    determined pivot. This is the descriptive generalization that the
    nominal licensing analysis (predicate fronting + Case on T) derives. -/
theorem prediction_matches_pivot :
    extractionData.all (λ d =>
      match d.extracted with
      | .dpArg _ =>
        (predictExtraction d.voice d.extracted == .grammatical)
          == d.extractsPivot
      | .adjunct => true) = true := by
  native_decide

-- ============================================================================
-- § 4: Structural Grounding
-- ============================================================================

/-- For DP arguments, the prediction function IS the pivot check — they
    agree extensionally on the extraction data. This grounds the
    descriptive generalization ("only pivots extract") in the licensing
    analysis ("only Case-licensed DPs can be Ā-extracted, and only the
    pivot is Case-licensed"). -/
theorem structural_grounding :
    extractionData.all (λ d =>
      match d.extracted with
      | .dpArg _ =>
        predictExtraction d.voice d.extracted ==
          if d.extractsPivot then .grammatical else .ungrammatical
      | .adjunct => true) = true := by
  native_decide

/-- The nominal licensing analysis predicts non-DPs extract freely:
    since non-DPs don't need Case, the Case-based restriction doesn't
    apply. This is the distinguishing prediction of §4.3. -/
theorem nonDP_unrestricted :
    ∀ v : Fragments.TobaBatak.Voice,
      predictExtraction v .adjunct = .grammatical := by
  intro v; rfl

end Phenomena.FillerGap.Studies.Erlewine2018

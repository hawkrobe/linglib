import Linglib.Phenomena.FillerGap.TobaBatak
import Linglib.Theories.Syntax.Minimalism.Core.Position

/-!
# Minimalism Bridge: Toba Batak Extraction Restriction @cite{erlewine-2018}

Connects the empirical extraction data from Toba Batak to the
Minimalist analysis in Erlewine (2018).

## The Analysis (Erlewine 2018, §3–4)

The extraction restriction follows from the interaction of probing
and nominal licensing:

1. **Predicate fronting** (§3.2): C bears `[PROBE:FOC]`, which attracts
   the closest `[+FOC]` constituent — normally the vP — to Spec,CP,
   deriving V-initial word order. The subject/pivot is stranded in
   Spec,TP after vP fronts.

2. **Nominal licensing** (§4): T bears `[PROBE:D]`, which Case-licenses
   the subject DP in Spec,TP. If a non-subject DP were attracted to
   Spec,CP by `[PROBE:FOC]`, it would end up in a position with no
   available Case licensor — the derivation crashes. Therefore only the
   pivot (already Case-licensed by T) can be Ā-extracted.

3. **Non-DP extraction is unrestricted** (§4.6): Since the restriction
   is about nominal licensing, non-DP constituents (adverbs, PPs) can
   freely front to Spec,CP regardless of voice.

The descriptive generalization is: extraction of a DP argument is
grammatical iff it is the pivot for the given voice.

## Connection to Mam (Elkins, Imanishi & Coon 2026)

Both TB and Mam involve successive-cyclic movement leaving
morphological traces at clause boundaries. The shared abstraction
is `CyclicChain` from Position.lean:

- **Mam**: Each intermediate Voice⁰ Agrees [+oblique], spelling out
  as =(y)a'. The chain entries correspond to feature-valuation events.
- **TB**: Each intermediate C⁰ shows extraction voice morphology,
  reflecting the passage of the wh-element through Spec,CP.

## References

- Erlewine, M. Y. (2018). Extraction and licensing in Toba Batak.
  Language 94(3): 662–697.
- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
-/

namespace Phenomena.FillerGap.Bridge.MinimalismTobaBatak

open Fragments.TobaBatak

-- ============================================================================
-- § 1: Prediction Function
-- ============================================================================

/-- Predict whether extraction is grammatical from voice + extracted role.

    The nominal licensing analysis predicts: extraction of a DP argument
    is grammatical iff it is the pivot, because only the pivot is
    Case-licensed (by T's [PROBE:D] in Spec,TP) before Ā-extraction. -/
def predictExtraction (voice : Fragments.TobaBatak.Voice) (extracted : Interfaces.ArgumentRole) :
    ExtractionJudgment :=
  if extracted == voice.pivotRole then .grammatical
  else .ungrammatical

-- ============================================================================
-- § 2: Per-Datum Bridge Theorems
-- ============================================================================

/-- AV + agent (pivot): Case-licensed in Spec,TP → extractable. -/
theorem bridge_av_agent :
    predictExtraction .av .agent = .grammatical ∧
    avAgentExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

/-- AV + patient (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_av_patient :
    predictExtraction .av .patient = .ungrammatical ∧
    avPatientExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

/-- AV + oblique (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_av_oblique :
    predictExtraction .av .oblique = .ungrammatical ∧
    avObliqueExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

/-- OV + patient (pivot): Case-licensed in Spec,TP → extractable. -/
theorem bridge_ov_patient :
    predictExtraction .ov .patient = .grammatical ∧
    ovPatientExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

/-- OV + agent (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_ov_agent :
    predictExtraction .ov .agent = .ungrammatical ∧
    ovAgentExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

/-- OV + oblique (non-pivot): no Case licensor in Spec,CP. -/
theorem bridge_ov_oblique :
    predictExtraction .ov .oblique = .ungrammatical ∧
    ovObliqueExtraction.judgment = .ungrammatical := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Completeness
-- ============================================================================

/-- The structural analysis correctly predicts every monoclausal datum. -/
theorem all_predictions_match :
    extractionData.all (λ d =>
      predictExtraction d.voice d.extracted == d.judgment) = true := by
  native_decide

/-- The prediction function agrees with extractsPivot: extraction is
    grammatical iff the extracted element is the voice-determined pivot.
    This is the descriptive generalization that the nominal licensing
    analysis (predicate fronting + Case on T) derives. -/
theorem prediction_matches_pivot :
    extractionData.all (λ d =>
      (predictExtraction d.voice d.extracted == .grammatical)
        == d.extractsPivot) = true := by
  native_decide

-- ============================================================================
-- § 4: Structural Grounding
-- ============================================================================

/-- The prediction function IS the pivot check — they agree extensionally
    on the extraction data. This grounds the descriptive generalization
    ("only pivots extract") in the licensing analysis ("only
    Case-licensed DPs can be Ā-extracted, and only the pivot is
    Case-licensed"). -/
theorem structural_grounding :
    extractionData.all (λ d =>
      predictExtraction d.voice d.extracted ==
        if d.extractsPivot then .grammatical else .ungrammatical) = true := by
  native_decide

end Phenomena.FillerGap.Bridge.MinimalismTobaBatak

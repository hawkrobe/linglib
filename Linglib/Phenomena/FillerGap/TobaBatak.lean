import Linglib.Fragments.TobaBatak.Basic

/-!
# Toba Batak Extraction Restriction @cite{erlewine-2018}

Theory-neutral empirical data on the extraction restriction in Toba
Batak: only the pivot can undergo Ā-movement (wh-movement,
relativization, clefting).

## Key Empirical Findings

1. **Pivot-only extraction**: Only the pivot argument can be
   Ā-extracted. All other arguments are trapped (§2).
2. **Voice determines pivot**: Actor Voice → agent is pivot;
   Object Voice → patient is pivot (§2.1).
3. **Voice symmetry**: AV makes the agent extractable but not the
   patient; OV makes the patient extractable but not the agent.
4. **Long-distance extraction**: The extracted element must be the
   pivot of the most deeply embedded clause, and intermediate clauses
   show extraction morphology (§4).

## Cross-Linguistic Context

Toba Batak's extraction restriction contrasts with:
- **Tagalog/Seediq** (Austronesian): Philippine-style voice/Case
  determines extraction via agreement morphology — a voice-as-case
  system. Erlewine (2018, §4.1) argues TB is NOT this type.
- **Mam** (Mayan): Extraction is unrestricted, but oblique extraction
  triggers a dedicated morpheme (=(y)a') as an Agree reflex on Voice⁰.
- **English**: No extraction restriction; gap strategy.

TB and Tagalog are both Austronesian and both use voice morphology,
but the mechanism differs: Tagalog has voice-as-Case, while TB has
predicate fronting + nominal licensing (DPs in Spec,CP lack a Case
licensor). Mam (Mayan) shows a third pattern: unrestricted extraction
with morphological reflexes of Agree.

## References

- Erlewine, M. Y. (2018). Extraction and licensing in Toba Batak.
  Language 94(3): 662–697.
-/

namespace Phenomena.FillerGap.TobaBatak

open Fragments.TobaBatak

-- ============================================================================
-- § 1: Data Count
-- ============================================================================

theorem extraction_data_count : extractionData.length = 8 := by native_decide

-- ============================================================================
-- § 2: Per-Datum Verification
-- ============================================================================

/-- AV + agent (pivot): grammatical. -/
theorem av_agent_grammatical :
    avAgentExtraction.judgment = .grammatical ∧
    avAgentExtraction.extractsPivot = true := ⟨rfl, rfl⟩

/-- AV + patient (non-pivot): ungrammatical. -/
theorem av_patient_ungrammatical :
    avPatientExtraction.judgment = .ungrammatical ∧
    avPatientExtraction.extractsPivot = false := ⟨rfl, rfl⟩

/-- AV + oblique (non-pivot): ungrammatical. -/
theorem av_oblique_ungrammatical :
    avObliqueExtraction.judgment = .ungrammatical ∧
    avObliqueExtraction.extractsPivot = false := ⟨rfl, rfl⟩

/-- OV + patient (pivot): grammatical. -/
theorem ov_patient_grammatical :
    ovPatientExtraction.judgment = .grammatical ∧
    ovPatientExtraction.extractsPivot = true := ⟨rfl, rfl⟩

/-- OV + agent (non-pivot): ungrammatical. -/
theorem ov_agent_ungrammatical :
    ovAgentExtraction.judgment = .ungrammatical ∧
    ovAgentExtraction.extractsPivot = false := ⟨rfl, rfl⟩

/-- OV + oblique (non-pivot): ungrammatical. -/
theorem ov_oblique_ungrammatical :
    ovObliqueExtraction.judgment = .ungrammatical ∧
    ovObliqueExtraction.extractsPivot = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2b: Per-Datum Verification (Adjuncts, §4.6)
-- ============================================================================

/-- AV + adjunct: grammatical (adjuncts don't need Case). -/
theorem av_adjunct_grammatical :
    avAdjunctExtraction.judgment = .grammatical := rfl

/-- OV + adjunct: grammatical (adjuncts don't need Case). -/
theorem ov_adjunct_grammatical :
    ovAdjunctExtraction.judgment = .grammatical := rfl

-- ============================================================================
-- § 3: Descriptive Generalizations
-- ============================================================================

/-- For DP arguments: extraction is grammatical iff the extracted
    element is the pivot for the given voice (§2). -/
theorem dp_extraction_iff_pivot :
    extractionData.all (λ d =>
      match d.extracted with
      | .dpArg _ => d.extractsPivot == (d.judgment == .grammatical)
      | .adjunct => true) = true := by
  native_decide

/-- For non-DP adjuncts: extraction is always grammatical regardless
    of voice, because adjuncts don't need Case licensing (§4.6). -/
theorem adjunct_always_grammatical :
    extractionData.all (λ d =>
      match d.extracted with
      | .adjunct => d.judgment == .grammatical
      | .dpArg _ => true) = true := by
  native_decide

/-- Voice symmetry: AV and OV are mirror images — each makes exactly
    one argument extractable (the pivot) and blocks all others. -/
theorem voice_symmetry :
    avAgentExtraction.judgment = .grammatical ∧
    ovPatientExtraction.judgment = .grammatical ∧
    avPatientExtraction.judgment = .ungrammatical ∧
    ovAgentExtraction.judgment = .ungrammatical := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Cross-Linguistic Comparison
-- ============================================================================

/-- TB uses structural restriction, not dedicated morpheme or voice
    alternation in the Tagalog sense. -/
theorem tb_strategy :
    tbExtractionProfile.strategy = .structuralRestriction := rfl

/-- TB distinguishes extracted positions via voice (which role is pivot). -/
theorem tb_distinguishes :
    tbExtractionProfile.distinguishesPosition = true := rfl

end Phenomena.FillerGap.TobaBatak

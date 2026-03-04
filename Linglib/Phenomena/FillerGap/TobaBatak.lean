import Linglib.Fragments.TobaBatak.Basic
import Linglib.Fragments.TobaBatak.Relativization
import Linglib.Core.Relativization.Extraction

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
  system. @cite{erlewine-2018} argues TB is NOT this type.
- **Mam** (Mayan): Extraction is unrestricted, but oblique extraction
  triggers a dedicated morpheme (=(y)a') as an Agree reflex on Voice⁰.
- **English**: No extraction restriction; gap strategy.

TB and Tagalog are both Austronesian and both use voice morphology,
but the mechanism differs: Tagalog has voice-as-Case, while TB has
predicate fronting + nominal licensing (DPs in Spec,CP lack a Case
licensor). Mam (Mayan) shows a third pattern: unrestricted extraction
with morphological reflexes of Agree.

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

-- ============================================================================
-- § 5: End-to-End Derivation Chain
-- ============================================================================

/-! ### Extraction data → ExtractionProfile → AH → Relativization

Connects three independent data sources through the AH bridge:
1. Individual extraction datums (from @cite{erlewine-2018})
2. The ExtractionProfile summary (markedPositions)
3. RelClauseMarkers (from @cite{keenan-comrie-1977})

If any link is wrong — e.g., listing `.directObject` as extractable when
relativization markers don't cover DO — the chain breaks.

Note: the extraction data uses `ArgumentRole` (agent, patient) while the
ExtractionProfile and AH use `ExtractionTarget` (subject, directObject).
Voice promotion means the patient's *default* position is DO, but its
*surface* extraction position is always subject (the pivot). The chain
must go through the ExtractionProfile, which encodes this fact. -/

/-- Link 1→2: The ExtractionProfile's marked positions are exactly the
    positions for which some voice makes a DP argument grammatically
    extractable. Only `.subject` qualifies (the pivot position). -/
theorem profile_matches_data :
    tbExtractionProfile.markedPositions.all (λ pos =>
      extractionData.any (λ d =>
        match d.extracted with
        | .dpArg role => role.defaultPosition == pos ∧
                         d.judgment == .grammatical ∧
                         d.extractsPivot
        | .adjunct => false)) = true := by
  native_decide

/-- Link 2→3: Every extractable position (ExtractionTarget) maps to an
    AH position that is covered by some Toba Batak relativization
    marker. Would have failed with the old `[.subject, .directObject]`
    because `.directObject` maps to `AHPosition.directObject`, which
    no marker covers. -/
theorem extractable_positions_are_relativizable :
    tbExtractionProfile.markedPositions.all (λ et =>
      let ahPos := Core.extractionTargetToAH et
      relMarkers.any (·.covers ahPos)) = true := by
  native_decide

/-- Full chain (all three links as a single conjunction):
    (1) every grammatical DP extraction extracts the pivot,
    (2) the pivot position (subject) is in `markedPositions`, and
    (3) every marked position maps to a relativizable AH position.
    Connects @cite{erlewine-2018}'s extraction data through the
    ExtractionProfile to @cite{keenan-comrie-1977}'s markers. -/
theorem extraction_profile_relativization_chain :
    -- Link 1: grammatical DP extraction ↔ pivot
    (extractionData.all (λ d =>
      match d.extracted with
      | .dpArg _ => d.extractsPivot == (d.judgment == .grammatical)
      | .adjunct => true)) ∧
    -- Link 2: pivot position (subject) is in markedPositions
    (tbExtractionProfile.marks .subject) ∧
    -- Link 3: every marked position is relativizable via AH
    (tbExtractionProfile.markedPositions.all (λ et =>
      let ahPos := Core.extractionTargetToAH et
      relMarkers.any (·.covers ahPos))) := by
  native_decide

end Phenomena.FillerGap.TobaBatak

import Linglib.Fragments.Mam.ExtractionMorphology
import Linglib.Core.Interfaces.ExtractionMorphology

/-!
# Oblique Extraction Data

Theory-neutral empirical data on oblique extraction morphology, collecting
cross-linguistic observations on how languages morphologically track the
extraction of oblique arguments.

## Mam (SJO)

The primary data comes from Elkins, Imanishi & Coon (2026). The optional
enclitic =(y)a' marks oblique extraction and is sensitive to clause size:
it is licensed in full clauses and aspectless complements (where Voice is
projected), but blocked in infinitival complements (where Voice is absent).

### Key Empirical Findings

1. **=(y)a' is oblique-specific**: Subject (AF) and object extraction do
   not trigger it (§3).
2. **=(y)a' is clause-size-sensitive**: Licensed iff Voice is projected (§6).
3. **Multiple spellout**: In long-distance extraction, =(y)a' can appear
   on both matrix and embedded predicates (Table 4, §6.2).
4. **Island-sensitive**: =(y)a' is blocked by islands, arguing against
   a resumptive analysis (§7.1).
5. **Not Agent Focus**: Co-occurs with passive *-njtz* (§7.2).
6. **Temporal obliques exempt**: 'when' does not trigger =(y)a' (§8.1).

## Cross-Linguistic Comparison

K'ichean languages (K'iche', Kaqchikel) use *wi* in a parallel role.
Key difference: K'ichean *wi* is analyzed as copy spellout,
while Mam =(y)a' is analyzed as an Agree reflex on Voice⁰/Dir⁰ (§8.2).

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
-/

namespace Phenomena.FillerGap.OblExtraction

open Fragments.Mam

-- ============================================================================
-- § 1: Monoclausal Data
-- ============================================================================

/-- Monoclausal extraction data points from Elkins et al. (2026). -/
def mamMonoData : List MamExtractionDatum := monoData

theorem mono_data_count : mamMonoData.length = 5 := by native_decide

-- ============================================================================
-- § 2: Per-Datum Verification (Monoclausal)
-- ============================================================================

/-- Full clause + oblique: =(y)a' licensed (§3.1, ex. 8). -/
theorem trans_obl_eqya :
    transOblExtraction.clauseType.projectsVoice = true ∧
    transOblExtraction.obliqueExtracted = true ∧
    transOblExtraction.judgment = .licensed := ⟨rfl, rfl, rfl⟩

/-- Full clause + subject: =(y)a' blocked; AF instead (§3.1, ex. 6). -/
theorem trans_subj_no_eqya :
    transSubjExtraction.obliqueExtracted = false ∧
    transSubjExtraction.judgment = .blocked := ⟨rfl, rfl⟩

/-- Full clause + object: =(y)a' blocked (§3.1, ex. 7). -/
theorem trans_obj_no_eqya :
    transObjExtraction.obliqueExtracted = false ∧
    transObjExtraction.judgment = .blocked := ⟨rfl, rfl⟩

/-- Passive + oblique: =(y)a' licensed even without agent (§4.1). -/
theorem passive_obl_eqya :
    passiveOblExtraction.clauseType.projectsVoice = true ∧
    passiveOblExtraction.judgment = .licensed := ⟨rfl, rfl⟩

/-- Temporal oblique: =(y)a' blocked — 'when' is exempt (§8.1). -/
theorem temporal_obl_no_eqya :
    temporalOblExtraction.judgment = .blocked := rfl

-- ============================================================================
-- § 3: Long-Distance Data (Table 4)
-- ============================================================================

/-- Long-distance extraction data from Table 4. -/
def mamLDData : List MamLongDistanceDatum := ldData

theorem ld_data_count : mamLDData.length = 4 := by native_decide

/-- LD from full CP: =(y)a' licensed on both matrix and embedded.
    The matrix clause projects Voice; the embedded CP also projects Voice.
    Each Voice⁰ independently Agrees → multiple =(y)a'. -/
theorem ld_full_cp_both :
    ldFullCP.matrixJudgment = .licensed ∧
    ldFullCP.embeddedJudgment = .licensed := ⟨rfl, rfl⟩

/-- LD from aspectless: =(y)a' licensed on both (embedded is VoiceP-sized). -/
theorem ld_aspectless_both :
    ldAspectless.matrixJudgment = .licensed ∧
    ldAspectless.embeddedJudgment = .licensed := ⟨rfl, rfl⟩

/-- LD from infinitival: =(y)a' licensed on matrix, BLOCKED on embedded.
    Embedded clause is VP-sized (no Voice) → no [uOblique] probe. -/
theorem ld_infinitival_matrix_only :
    ldInfinitival.matrixJudgment = .licensed ∧
    ldInfinitival.embeddedJudgment = .blocked := ⟨rfl, rfl⟩

/-- Embedded question: =(y)a' blocked on matrix, licensed on embedded.
    Oblique moves within the embedded clause only — does not pass through
    matrix Spec,VoiceP. -/
theorem ld_eq_embedded_only :
    ldEmbeddedQuestion.matrixJudgment = .blocked ∧
    ldEmbeddedQuestion.embeddedJudgment = .licensed := ⟨rfl, rfl⟩

-- ============================================================================
-- § 4: Generalizations
-- ============================================================================

/-- =(y)a' tracks oblique, not extraction in general: subject and object
    extraction in the same clause type do not trigger it. -/
theorem eqya_oblique_specific :
    transSubjExtraction.clauseType = transOblExtraction.clauseType ∧
    transObjExtraction.clauseType = transOblExtraction.clauseType ∧
    transSubjExtraction.judgment = .blocked ∧
    transObjExtraction.judgment = .blocked ∧
    transOblExtraction.judgment = .licensed := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- In LD extraction, =(y)a' is licensed on the embedded predicate iff
    the embedded clause projects Voice. -/
theorem ld_embedded_tracks_voice :
    ldData.all (λ d =>
      d.embeddedClauseType.projectsVoice == (d.embeddedJudgment == .licensed)) = true := by
  native_decide

/-- Island sensitivity: =(y)a' is blocked by syntactic islands (§7.1,
    ex. 50–52). This argues against a resumptive-pronoun analysis, since
    resumptives typically rescue island violations. -/
theorem eqya_island_sensitive : eqyaIslandSensitive = true := rfl

/-- =(y)a' co-occurs with passive *-njtz* (§7.2, ex. 53–54), while
    Agent Focus *-a* is in complementary distribution with voice
    morphemes. Therefore =(y)a' ≠ AF. -/
theorem eqya_cooccurs_with_passive : eqyaCooccursWithPassive = true := rfl

-- ============================================================================
-- § 5: Cross-Linguistic Comparison (Mam vs. K'ichean)
-- ============================================================================

/-- K'iche' extraction marker *wi*. -/
def kicheExtractionProfile : Interfaces.ExtractionProfile :=
  { language := "K'iche'"
  , strategy := .dedicatedMorpheme
  , markedPositions := [.oblique]
  , distinguishesPosition := true
  , notes := "Fronting particle wi marks oblique extraction; " ++
             "analyzed as copy spellout, unlike " ++
             "Mam =(y)a' which is Agree on Voice/Dir (Elkins et al. §8.2)" }

/-- Both Mam and K'iche' use dedicated morphemes for oblique extraction,
    but via different mechanisms (Agree vs. copy spellout). -/
theorem mayan_oblique_extraction_pattern :
    mamExtractionProfile.strategy = .dedicatedMorpheme ∧
    kicheExtractionProfile.strategy = .dedicatedMorpheme := ⟨rfl, rfl⟩

end Phenomena.FillerGap.OblExtraction

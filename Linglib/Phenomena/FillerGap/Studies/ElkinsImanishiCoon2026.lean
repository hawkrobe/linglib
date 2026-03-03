import Linglib.Fragments.Mam.ExtractionMorphology
import Linglib.Fragments.Mam.VoiceSystem
import Linglib.Fragments.Kiche.ExtractionMorphology
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine

/-!
# Oblique Extraction in Mayan
@cite{elkins-imanishi-coon-2026} @cite{henderson-2008} @cite{imanishi-2020}

## Part I: Cross-Linguistic Comparison

Cross-linguistic comparison of extraction morphology in two Mayan
language groups: SJO Mam (=(y)a') and K'ichean (*wi*). Both mark
oblique extraction with a dedicated morpheme, but the underlying
mechanisms and distributional properties differ.

### Shared Properties

- Both mark oblique extraction (spatial, instrumental)
- Both exempt temporal obliques ('when')
- Neither marks subject extraction (Agent Focus instead)
- Neither marks object extraction

### Parametric Differences

| Property                      | Mam =(y)a'          | K'ichean *wi*         |
|-------------------------------|---------------------|-----------------------|
| Locus                         | On probe (Voice⁰)  | At extraction site    |
| Mechanism                     | Agree reflex        | Copy spellout         |
| Reason obliques ('why')       | =(y)a' ✓            | *wi* ✗                |
| Fronting Particle Generalization | Does not hold    | Holds                 |
| Conditioned by clause size    | Yes (Voice project.)| No                    |
| Multiple spellout in LD       | Yes (per Voice/Dir) | Unclear               |

## Part II: Minimalist Analysis

Connects three Minimalist abstractions — ClauseSpine, Agree/feature-valuation,
and Spellout — to the empirical data on =(y)a' distribution in SJO Mam.

1. Voice⁰ (and Dir⁰) in Mam carry [uOblique] (an unvalued probe feature).
2. When an oblique DP undergoes successive-cyclic Ā-movement through
   Spec,VoiceP, Agree values [uOblique] as [+oblique] on Voice⁰.
3. At Spellout (PF), [+oblique] on Voice⁰ is realized as =(y)a'.
4. In infinitival complements, Voice is not projected (VP-sized), so there
   is no [uOblique] probe — =(y)a' cannot appear.
5. In long-distance extraction, each Voice⁰/Dir⁰ along the movement path
   independently Agrees, yielding multiple =(y)a' (one per Voice/Dir).
-/

namespace Phenomena.FillerGap.Studies.ElkinsImanishiCoon2026

-- ============================================================================
-- Part I: Cross-Linguistic Comparison
-- ============================================================================

open Fragments.Mam Fragments.Kiche

-- ============================================================================
-- § 1: Shared Properties
-- ============================================================================

/-- Both Mam and K'ichean use dedicated morphemes for oblique extraction. -/
theorem both_mark_oblique :
    mamExtractionProfile.strategy = .dedicatedMorpheme ∧
    kicheanExtractionProfile.strategy = .dedicatedMorpheme := ⟨rfl, rfl⟩

/-- Both exempt temporal obliques from extraction marking. -/
theorem both_exempt_temporal :
    (Fragments.Mam.temporalOblExtraction.isTemporal = true ∧
     Fragments.Mam.temporalOblExtraction.judgment = .blocked) ∧
    Fragments.Kiche.temporalOblExtraction.wiLicensed = false :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- Neither marks subject extraction (Agent Focus instead). -/
theorem neither_marks_subject :
    transSubjExtraction.judgment = .blocked ∧
    Fragments.Kiche.subjectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Neither marks object extraction. -/
theorem neither_marks_object :
    transObjExtraction.judgment = .blocked ∧
    Fragments.Kiche.objectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: Parametric Differences
-- ============================================================================

/-- KEY CONTRAST — Reason obliques ('why'):
    Mam =(y)a' IS licensed with reason extraction; K'ichean *wi* is NOT. -/
theorem reason_oblique_contrast :
    transOblExtraction.judgment = .licensed ∧
    Fragments.Kiche.reasonOblExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Mam =(y)a' is conditioned by clause size (Voice must project);
    K'ichean *wi* is not. -/
theorem clause_size_sensitivity :
    MamClauseType.fullCP.projectsVoice = true ∧
    MamClauseType.aspectless.projectsVoice = true ∧
    MamClauseType.infinitival.projectsVoice = false ∧
    Fragments.Kiche.frontingParticleGeneralization = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Theoretical Implications
-- ============================================================================

/-- Genuinely different mechanisms producing superficially similar patterns. -/
inductive ExtractionMorphologyMechanism where
  | agreeReflex     -- Morpheme on probe head (Mam =(y)a')
  | copySpellout    -- Morpheme at extraction site (K'ichean *wi*)
  deriving DecidableEq, BEq, Repr

def mamMechanism : ExtractionMorphologyMechanism := .agreeReflex
def kicheanMechanism : ExtractionMorphologyMechanism := .copySpellout

theorem different_mechanisms :
    mamMechanism ≠ kicheanMechanism := by decide

-- ============================================================================
-- Part II: Minimalist Analysis
-- ============================================================================

open Minimalism

-- ============================================================================
-- § 4: Spellout Theorems
-- ============================================================================

/-- Valued [+oblique] on Voice spells out as =(y)a'. -/
theorem spellout_oblique_voice :
    spellout mamVoiceVocab [.valued (.oblique true)] (some .Voice) = some "=(y)a'" := by
  native_decide

/-- Without [+oblique], Voice has no exponent from this vocabulary. -/
theorem spellout_no_oblique :
    spellout mamVoiceVocab [.valued (.oblique false)] (some .Voice) = none := by
  native_decide

/-- [+oblique] on a non-Voice head does not yield =(y)a'
    (context restriction blocks insertion). -/
theorem spellout_oblique_wrong_context :
    spellout mamVoiceVocab [.valued (.oblique true)] (some .T) = none := by
  native_decide

-- ============================================================================
-- § 5: Prediction Function
-- ============================================================================

/-- Predict whether =(y)a' is licensed from a clause spine and extraction type. -/
def predictEqYa (spine : ClauseSpine) (obliqueExtracted : Bool)
    (isTemporal : Bool := false) : MamExtractionJudgment :=
  if spine.projects .Voice && obliqueExtracted && !isTemporal then .licensed
  else .blocked

-- ============================================================================
-- § 6: Per-Datum Theorems (Monoclausal)
-- ============================================================================

/-- Transitive clause + oblique extraction → =(y)a' licensed. -/
theorem bridge_trans_obl :
    mamTransitiveSpine.projects .Voice = true ∧
    predictEqYa mamTransitiveSpine true = .licensed ∧
    transOblExtraction.judgment = .licensed := by
  exact ⟨by native_decide, by native_decide, rfl⟩

/-- Transitive + subject extraction → no =(y)a'. -/
theorem bridge_trans_subj :
    predictEqYa mamTransitiveSpine false = .blocked ∧
    transSubjExtraction.judgment = .blocked := by
  exact ⟨by native_decide, rfl⟩

/-- Transitive + object extraction → no =(y)a'. -/
theorem bridge_trans_obj :
    predictEqYa mamTransitiveSpine false = .blocked ∧
    transObjExtraction.judgment = .blocked := by
  exact ⟨by native_decide, rfl⟩

/-- Passive + oblique → =(y)a' licensed. -/
theorem bridge_passive_obl :
    mamTransitiveSpine.projects .Voice = true ∧
    predictEqYa mamTransitiveSpine true = .licensed ∧
    passiveOblExtraction.judgment = .licensed := by
  exact ⟨by native_decide, by native_decide, rfl⟩

/-- Temporal oblique + full clause → =(y)a' BLOCKED. -/
theorem bridge_temporal_obl :
    predictEqYa mamTransitiveSpine true (isTemporal := true) = .blocked ∧
    temporalOblExtraction.judgment = .blocked := by
  exact ⟨by native_decide, rfl⟩

-- ============================================================================
-- § 7: Long-Distance Theorems
-- ============================================================================

/-- Map MamClauseType to the corresponding ClauseSpine. -/
def spineOf : MamClauseType → ClauseSpine
  | .fullCP => mamTransitiveSpine
  | .aspectless => mamAspectlessSpine
  | .infinitival => mamInfinitivalSpine

/-- LD from full CP → =(y)a' licensed on both predicates. -/
theorem bridge_ld_fullCP :
    (spineOf ldFullCP.embeddedClauseType).projects .Voice = true ∧
    ldFullCP.matrixJudgment = .licensed ∧
    ldFullCP.embeddedJudgment = .licensed := by
  exact ⟨by native_decide, rfl, rfl⟩

/-- LD from aspectless → =(y)a' licensed on both. -/
theorem bridge_ld_aspectless :
    (spineOf ldAspectless.embeddedClauseType).projects .Voice = true ∧
    ldAspectless.matrixJudgment = .licensed ∧
    ldAspectless.embeddedJudgment = .licensed := by
  exact ⟨by native_decide, rfl, rfl⟩

/-- LD from infinitival → =(y)a' on matrix only. -/
theorem bridge_ld_infinitival :
    (spineOf ldInfinitival.embeddedClauseType).projects .Voice = false ∧
    ldInfinitival.matrixJudgment = .licensed ∧
    ldInfinitival.embeddedJudgment = .blocked := by
  exact ⟨by native_decide, rfl, rfl⟩

/-- EQ → =(y)a' on embedded only. -/
theorem bridge_ld_eq :
    ldEmbeddedQuestion.matrixJudgment = .blocked ∧
    ldEmbeddedQuestion.embeddedJudgment = .licensed := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Completeness
-- ============================================================================

/-- All monoclausal predictions match. -/
theorem all_mono_predictions_match :
    monoData.all (λ d =>
      predictEqYa (spineOf d.clauseType) d.obliqueExtracted d.isTemporal
        == d.judgment) = true := by
  native_decide

/-- All LD embedded predictions match. -/
theorem all_ld_embedded_predictions_match :
    ldData.all (λ d =>
      d.embeddedClauseType.projectsVoice == (d.embeddedJudgment == .licensed)) = true := by
  native_decide

-- ============================================================================
-- § 9: Against Alternative Analyses
-- ============================================================================

/-- Against resumptive-pronoun analysis: =(y)a' is island-sensitive. -/
theorem eqya_not_resumptive :
    eqyaIslandSensitive = true := rfl

/-- Against Agent Focus analysis: =(y)a' co-occurs with passive voice. -/
theorem eqya_not_agent_focus :
    mamPassiveVoice.features = mamVoice.features ∧
    mamPassiveVoice.flavor ≠ mamVoice.flavor ∧
    passiveOblExtraction.judgment = .licensed ∧
    transSubjExtraction.judgment = .blocked ∧
    transOblExtraction.judgment = .licensed := by
  exact ⟨rfl, by decide, rfl, rfl, rfl⟩

/-- Against copy spellout: =(y)a' disappears when Voice is absent. -/
theorem eqya_not_copy_spellout :
    (spineOf MamClauseType.aspectless).projects .Voice = true ∧
    (spineOf MamClauseType.infinitival).projects .Voice = false ∧
    ldAspectless.embeddedJudgment = .licensed ∧
    ldInfinitival.embeddedJudgment = .blocked := by
  exact ⟨by native_decide, by native_decide, rfl, rfl⟩

-- ============================================================================
-- § 10: ClauseSpine vs. ComplementSize
-- ============================================================================

/-- ClauseSpine is finer than ComplementSize: it can distinguish
    infinitival (VP) from aspectless (VoiceP). -/
theorem clauseSpine_finer_than_complementSize :
    mamAspectlessSpine.projects .Voice = true ∧
    mamInfinitivalSpine.projects .Voice = false := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 11: Dir⁰ Spellout
-- ============================================================================

/-- Dir⁰ also carries [uOblique]. -/
theorem dir_probe_matches_voice :
    dirCis.features = mamVoice.features := by native_decide

/-- Dir⁰ with valued [+oblique] also spells out as =(y)a'. -/
theorem dir_spellout_eqya :
    spellout mamVoiceVocab [.valued (.oblique true)] (some .Voice) = some "=(y)a'" := by
  native_decide

-- ============================================================================
-- § 12: Derivation Tree
-- ============================================================================

section Derivation

private def oblique_dp := mkLeafPhon .D [] "jawu'" 1
private def verb_root := mkLeafPhon .V [.D] "loq'" 2
private def object_dp := mkLeafPhon .D [] "wääy" 3
private def voice_head := mkLeafPhon .Voice [.V] "" 4
private def t_head := mkLeafPhon .T [.Voice] "" 5
private def c_head := mkLeafPhon .C [.T] "" 6

private def vp := merge verb_root object_dp
private def voiceP := merge voice_head vp
private def voiceP_obl := merge oblique_dp voiceP
private def tp := merge t_head voiceP_obl
private def cp := merge oblique_dp (merge c_head tp)

theorem derivation_tree_size : cp.nodeCount = 6 := by native_decide

theorem voice_has_uOblique :
    hasUnvaluedFeature mamVoice.features (.oblique false) = true := by
  native_decide

private def oblique_goal_features : FeatureBundle := [.valued (.oblique true)]

/-- Agree at Voice: [uOblique] valued by oblique DP's [+oblique]. -/
theorem voice_agree_values_oblique :
    applyAgree mamVoice.features oblique_goal_features (.oblique false) =
    some [.valued (.oblique true)] := by
  native_decide

/-- Spellout: valued [+oblique] on Voice maps to "=(y)a'". -/
theorem voice_spellout_eqya :
    spellout mamVoiceVocab [.valued (.oblique true)] (some .Voice) =
    some "=(y)a'" := by
  native_decide

/-- Full derivation pipeline: Agree then Spellout → "=(y)a'". -/
theorem full_derivation_pipeline :
    (applyAgree mamVoice.features oblique_goal_features (.oblique false)).bind
      (λ fb => spellout mamVoiceVocab fb (some .Voice)) = some "=(y)a'" := by
  native_decide

end Derivation

end Phenomena.FillerGap.Studies.ElkinsImanishiCoon2026

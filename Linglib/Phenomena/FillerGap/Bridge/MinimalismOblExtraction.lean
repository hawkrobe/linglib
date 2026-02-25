import Linglib.Phenomena.FillerGap.OblExtraction
import Linglib.Fragments.Mam.VoiceSystem
import Linglib.Theories.Syntax.Minimalism.Core.Spellout
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine

/-!
# Minimalism Bridge: Oblique Extraction in Mam

Connects three Minimalist abstractions — ClauseSpine, Agree/feature-valuation,
and Spellout — to the empirical data on =(y)a' distribution in SJO Mam.

## The Analysis (Elkins, Imanishi & Coon 2026)

1. Voice⁰ (and Dir⁰) in Mam carry [uOblique] (an unvalued probe feature).
2. When an oblique DP undergoes successive-cyclic Ā-movement through
   Spec,VoiceP, Agree values [uOblique] as [+oblique] on Voice⁰.
3. At Spellout (PF), [+oblique] on Voice⁰ is realized as =(y)a'.
4. In infinitival complements, Voice is not projected (VP-sized), so there
   is no [uOblique] probe — =(y)a' cannot appear.
5. In long-distance extraction, each Voice⁰/Dir⁰ along the movement path
   independently Agrees, yielding multiple =(y)a' (one per Voice/Dir).

This bridge proves that the theory correctly predicts each data point:
- Full clause + oblique extraction → =(y)a' licensed ✓
- Full clause + non-oblique extraction → no =(y)a' ✓
- Aspectless + oblique extraction → =(y)a' licensed ✓
- Infinitival + oblique extraction → no =(y)a' ✓
- LD from full CP: =(y)a' on both matrix and embedded ✓
- LD from infinitival: =(y)a' on matrix only ✓

## Against Alternatives (§7)

- **Not resumptive**: =(y)a' is island-sensitive (§7.1, ex. 50–52)
- **Not Agent Focus**: =(y)a' co-occurs with passive *-njtz* (§7.2, ex. 53–54),
  while AF *-a* is in complementary distribution with voice morphemes
- **Not copy spellout**: =(y)a' appears on Voice/Dir (the probe), not in the
  extraction site (the copy)

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
-/

namespace Phenomena.FillerGap.Bridge.MinimalismOblExtraction

open Minimalism Fragments.Mam

-- ============================================================================
-- § 1: Spellout Vocabulary for =(y)a'
-- ============================================================================

/-- Vocabulary entry for =(y)a': maps [+oblique] on Voice⁰ to the exponent
    "=(y)a'". This is the Vocabulary Insertion rule in DM terms. -/
def eqYaVocab : VocabEntry :=
  { features := [.valued (.oblique true)]
  , exponent := "=(y)a'"
  , context := some .Voice }

/-- The Mam Voice vocabulary: just the =(y)a' entry. -/
def mamVoiceVocab : Vocabulary := [eqYaVocab]

-- ============================================================================
-- § 2: Spellout Theorems
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
-- § 3: Prediction Function
-- ============================================================================

/-- Predict whether =(y)a' is licensed from a clause spine and extraction type.
    =(y)a' is licensed iff Voice is projected AND an oblique is extracted. -/
def predictEqYa (spine : ClauseSpine) (obliqueExtracted : Bool) : MamExtractionJudgment :=
  if spine.projects .Voice && obliqueExtracted then .licensed
  else .blocked

-- ============================================================================
-- § 4: Per-Datum Bridge Theorems (Monoclausal)
-- ============================================================================

/-- Bridge: transitive clause + oblique extraction → =(y)a' licensed.
    Theory: transitive spine projects Voice, oblique Agrees [+oblique]. -/
theorem bridge_trans_obl :
    mamTransitiveSpine.projects .Voice = true ∧
    predictEqYa mamTransitiveSpine true = .licensed ∧
    transOblExtraction.judgment = .licensed := by
  exact ⟨by native_decide, by native_decide, rfl⟩

/-- Bridge: transitive + subject extraction → no =(y)a'. -/
theorem bridge_trans_subj :
    predictEqYa mamTransitiveSpine false = .blocked ∧
    transSubjExtraction.judgment = .blocked := by
  exact ⟨by native_decide, rfl⟩

/-- Bridge: transitive + object extraction → no =(y)a'. -/
theorem bridge_trans_obj :
    predictEqYa mamTransitiveSpine false = .blocked ∧
    transObjExtraction.judgment = .blocked := by
  exact ⟨by native_decide, rfl⟩

/-- Bridge: passive + oblique → =(y)a' licensed.
    Passive still projects Voice (VoiceFlavor may differ, but Voice⁰ is present). -/
theorem bridge_passive_obl :
    mamTransitiveSpine.projects .Voice = true ∧
    predictEqYa mamTransitiveSpine true = .licensed ∧
    passiveOblExtraction.judgment = .licensed := by
  exact ⟨by native_decide, by native_decide, rfl⟩

-- ============================================================================
-- § 5: Long-Distance Bridge Theorems (Table 4)
-- ============================================================================

/-- Map MamClauseType to the corresponding ClauseSpine. -/
def spineOf : MamClauseType → ClauseSpine
  | .fullCP => mamTransitiveSpine
  | .aspectless => mamAspectlessSpine
  | .infinitival => mamInfinitivalSpine

/-- Bridge: LD from full CP → =(y)a' licensed on both predicates.
    Both matrix and embedded project Voice. -/
theorem bridge_ld_fullCP :
    (spineOf ldFullCP.embeddedClauseType).projects .Voice = true ∧
    ldFullCP.matrixJudgment = .licensed ∧
    ldFullCP.embeddedJudgment = .licensed := by
  exact ⟨by native_decide, rfl, rfl⟩

/-- Bridge: LD from aspectless → =(y)a' licensed on both.
    Aspectless embeds project Voice (VoiceP-sized). -/
theorem bridge_ld_aspectless :
    (spineOf ldAspectless.embeddedClauseType).projects .Voice = true ∧
    ldAspectless.matrixJudgment = .licensed ∧
    ldAspectless.embeddedJudgment = .licensed := by
  exact ⟨by native_decide, rfl, rfl⟩

/-- Bridge: LD from infinitival → =(y)a' on matrix only.
    Infinitival is VP-sized (no Voice). -/
theorem bridge_ld_infinitival :
    (spineOf ldInfinitival.embeddedClauseType).projects .Voice = false ∧
    ldInfinitival.matrixJudgment = .licensed ∧
    ldInfinitival.embeddedJudgment = .blocked := by
  exact ⟨by native_decide, rfl, rfl⟩

/-- Bridge: EQ → =(y)a' on embedded only.
    Oblique moves within the embedded clause; does not pass through
    matrix Spec,VoiceP (it's an embedded question, not LD extraction). -/
theorem bridge_ld_eq :
    ldEmbeddedQuestion.matrixJudgment = .blocked ∧
    ldEmbeddedQuestion.embeddedJudgment = .licensed := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Completeness
-- ============================================================================

/-- The theoretical prediction matches the empirical judgment for every
    monoclausal data point. -/
theorem all_mono_predictions_match :
    monoData.all (λ d =>
      predictEqYa (spineOf d.clauseType) d.obliqueExtracted == d.judgment) = true := by
  native_decide

/-- For long-distance data, the embedded predicate's =(y)a' status is
    predicted by whether the embedded clause projects Voice. -/
theorem all_ld_embedded_predictions_match :
    ldData.all (λ d =>
      d.embeddedClauseType.projectsVoice == (d.embeddedJudgment == .licensed)) = true := by
  native_decide

-- ============================================================================
-- § 7: Against Alternative Analyses
-- ============================================================================

/-- Against resumptive-pronoun analysis (§7.1):
    =(y)a' is island-sensitive — it is blocked by syntactic islands.
    Resumptive pronouns typically rescue island violations (Sells 1984),
    so island sensitivity argues that =(y)a' is a reflex of movement,
    not resumption. -/
theorem eqya_not_resumptive :
    eqyaIslandSensitive = true := rfl

/-- Against Agent Focus analysis (§7.2):
    =(y)a' co-occurs with passive voice morphology (*-njtz*), while
    Agent Focus (*-a*) is in complementary distribution with other voice
    morphemes. If =(y)a' were AF, it could not co-occur with passive.
    Additionally, in LD extraction, AF *-a* is restricted to the embedded
    clause, while =(y)a' appears on both matrix and embedded predicates. -/
theorem eqya_not_agent_focus :
    eqyaCooccursWithPassive = true ∧
    -- AF targets subjects; =(y)a' targets obliques
    transSubjExtraction.judgment = .blocked ∧
    transOblExtraction.judgment = .licensed := ⟨rfl, rfl, rfl⟩

/-- Against copy spellout (cf. K'ichean *wi*):
    =(y)a' is hosted on the probe (Voice⁰/Dir⁰), not the copy. Evidence:
    when Voice is absent (infinitival), =(y)a' disappears even though the
    oblique's base position still exists. Under copy spellout, the morpheme
    should appear at the copy regardless of clause size. -/
theorem eqya_not_copy_spellout :
    -- Same extraction type, different =(y)a' status → locus is Voice, not copy
    (spineOf MamClauseType.aspectless).projects .Voice = true ∧
    (spineOf MamClauseType.infinitival).projects .Voice = false ∧
    ldAspectless.embeddedJudgment = .licensed ∧
    ldInfinitival.embeddedJudgment = .blocked := by
  exact ⟨by native_decide, by native_decide, rfl, rfl⟩

-- ============================================================================
-- § 8: ClauseSpine vs. ComplementSize
-- ============================================================================

/-- ComplementSize cannot distinguish infinitival (VP) from aspectless (VoiceP):
    both have highest heads at F-level ≤ 1. ClauseSpine can distinguish them
    by checking whether Voice is projected. -/
theorem clauseSpine_finer_than_complementSize :
    mamAspectlessSpine.projects .Voice = true ∧
    mamInfinitivalSpine.projects .Voice = false := by
  exact ⟨by native_decide, by native_decide⟩

end Phenomena.FillerGap.Bridge.MinimalismOblExtraction

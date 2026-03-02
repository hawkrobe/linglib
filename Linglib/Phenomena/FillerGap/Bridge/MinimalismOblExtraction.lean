import Linglib.Fragments.Mam.ExtractionMorphology
import Linglib.Fragments.Mam.VoiceSystem
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine

/-!
# Minimalism Bridge: Oblique Extraction in Mam
@cite{elkins-imanishi-coon-2026}

Connects three Minimalist abstractions — ClauseSpine, Agree/feature-valuation,
and Spellout — to the empirical data on =(y)a' distribution in SJO Mam.

## The Analysis

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

-/

namespace Phenomena.FillerGap.Bridge.MinimalismOblExtraction

open Minimalism Fragments.Mam

-- ============================================================================
-- § 1: Spellout Theorems
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
    =(y)a' is licensed iff Voice is projected AND a non-temporal oblique is
    extracted. The `isTemporal` exclusion is a stipulation — the paper does
    not explain why temporal obliques are exempt (§8.1). -/
def predictEqYa (spine : ClauseSpine) (obliqueExtracted : Bool)
    (isTemporal : Bool := false) : MamExtractionJudgment :=
  if spine.projects .Voice && obliqueExtracted && !isTemporal then .licensed
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

/-- Bridge: temporal oblique + full clause → =(y)a' BLOCKED.
    Theory predicts blocking: temporal obliques are exempt (§8.1, stipulated).
    This honestly encodes the temporal exemption as a separate condition. -/
theorem bridge_temporal_obl :
    predictEqYa mamTransitiveSpine true (isTemporal := true) = .blocked ∧
    temporalOblExtraction.judgment = .blocked := by
  exact ⟨by native_decide, rfl⟩

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
    monoclausal data point. The `isTemporal` field is passed through to
    capture the temporal oblique exemption. -/
theorem all_mono_predictions_match :
    monoData.all (λ d =>
      predictEqYa (spineOf d.clauseType) d.obliqueExtracted d.isTemporal
        == d.judgment) = true := by
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
    Resumptive pronouns typically rescue island violations,
    so island sensitivity argues that =(y)a' is a reflex of movement,
    not resumption. -/
theorem eqya_not_resumptive :
    eqyaIslandSensitive = true := rfl

/-- Against Agent Focus analysis (§7.2):
    =(y)a' co-occurs with passive voice morphology (*-njtz*), while
    Agent Focus (*-a*) is in complementary distribution with other voice
    morphemes. If =(y)a' were AF, it could not co-occur with passive.

    The co-occurrence is *derived* from VoiceHead field independence:
    passive Voice differs in flavor (.nonThematic) but carries the same
    [uOblique] features as agentive Voice. =(y)a' is conditioned by
    features, *-njtz* by flavor — structurally orthogonal. -/
theorem eqya_not_agent_focus :
    -- Passive Voice carries the same oblique probe as agentive Voice
    mamPassiveVoice.features = mamVoice.features ∧
    -- But differs in flavor (what *-njtz* tracks)
    mamPassiveVoice.flavor ≠ mamVoice.flavor ∧
    -- Passive + oblique extraction is licensed (empirical confirmation)
    passiveOblExtraction.judgment = .licensed ∧
    -- AF targets subjects; =(y)a' targets obliques
    transSubjExtraction.judgment = .blocked ∧
    transOblExtraction.judgment = .licensed := by
  exact ⟨rfl, by decide, rfl, rfl, rfl⟩

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

-- ============================================================================
-- § 9: Dir⁰ Spellout — Parallel Probe on Directional Auxiliary
-- ============================================================================

/-- Dir⁰ also carries [uOblique] (Elkins et al. §3.1, §4.5).
    When an oblique passes through Dir's domain, Dir independently
    Agrees, yielding a second =(y)a' on the directional auxiliary.

    Dir's probe features are the same as Voice's — both carry [uOblique].
    This ensures both heads can trigger =(y)a' independently. -/
theorem dir_probe_matches_voice :
    dirCis.features = mamVoice.features := by native_decide

/-- Dir⁰ with valued [+oblique] also spells out as =(y)a'.
    The vocabulary entry is the same, but Dir is language-specific
    (not in `Cat`), so we check spellout with Voice context since
    Dir occupies V1 in the verbal template. -/
theorem dir_spellout_eqya :
    spellout mamVoiceVocab [.valued (.oblique true)] (some .Voice) = some "=(y)a'" := by
  native_decide

-- ============================================================================
-- § 10: Derivation Tree — Monoclausal Transitive Oblique Extraction
-- ============================================================================

section Derivation

/-! Models Tree 27 from @cite{elkins-imanishi-coon-2026}, §5.

The derivation shows the three key steps of the analysis:
1. Voice⁰ enters the derivation with [uOblique]
2. The oblique DP moves to Spec,VoiceP; Agree values [uOblique] → [+oblique]
3. At Spellout, [+oblique] on Voice⁰ is realized as =(y)a'

This connects the abstract prediction function (`predictEqYa`) to an
explicit Minimalist derivation using `SyntacticObject`, `merge`, `applyAgree`,
and `spellout`. -/

-- Lexical items as SyntacticObject nodes
private def oblique_dp := mkLeafPhon .D [] "jawu'" 1     -- 'where'
private def verb_root := mkLeafPhon .V [.D] "loq'" 2     -- 'buy'
private def object_dp := mkLeafPhon .D [] "wääy" 3       -- 'tortillas'
private def voice_head := mkLeafPhon .Voice [.V] "" 4    -- Voice⁰
private def t_head := mkLeafPhon .T [.Voice] "" 5        -- T⁰
private def c_head := mkLeafPhon .C [.T] "" 6            -- C⁰

-- Build the tree bottom-up (simplified; omits Dir, Appl, v for clarity)

/-- Step 1: VP — V merges with object. Oblique is base-generated as
    complement of V (or adjunct — structurally internal to VP). -/
private def vp := merge verb_root object_dp

/-- Step 2: VoiceP — Voice merges with VP. Voice carries [uOblique]. -/
private def voiceP := merge voice_head vp

/-- Step 3: Move oblique to Spec,VoiceP (internal merge).
    At this point, Voice Agrees with the oblique in its specifier. -/
private def voiceP_obl := merge oblique_dp voiceP

/-- Step 4: TP — T merges with VoiceP-with-extraction. -/
private def tp := merge t_head voiceP_obl

/-- Step 5: CP — Move oblique to Spec,CP (final landing site). -/
private def cp := merge oblique_dp (merge c_head tp)

-- The derivation produces a well-formed tree (6 Merge operations)
theorem derivation_tree_size : cp.nodeCount = 6 := by native_decide

-- Voice⁰ has [uOblique] (from the Mam Voice fragment)
theorem voice_has_uOblique :
    hasUnvaluedFeature mamVoice.features (.oblique false) = true := by
  native_decide

-- Features on the oblique DP: [+oblique] (interpretable on the goal)
private def oblique_goal_features : FeatureBundle := [.valued (.oblique true)]

/-- Agree at Voice: [uOblique] on Voice is valued by the oblique DP's
    [+oblique]. `applyAgree` copies the valued feature from goal to probe. -/
theorem voice_agree_values_oblique :
    applyAgree mamVoice.features oblique_goal_features (.oblique false) =
    some [.valued (.oblique true)] := by
  native_decide

/-- Spellout: valued [+oblique] on Voice maps to "=(y)a'" via
    Vocabulary Insertion (Elsewhere Condition; Spellout.lean). -/
theorem voice_spellout_eqya :
    spellout mamVoiceVocab [.valued (.oblique true)] (some .Voice) =
    some "=(y)a'" := by
  native_decide

/-- Full derivation pipeline: Voice Agrees with oblique, then valued
    features are spelled out as =(y)a'. This connects the SyntacticObject
    derivation to the morphological surface form in a single theorem. -/
theorem full_derivation_pipeline :
    (applyAgree mamVoice.features oblique_goal_features (.oblique false)).bind
      (λ fb => spellout mamVoiceVocab fb (some .Voice)) = some "=(y)a'" := by
  native_decide

end Derivation

end Phenomena.FillerGap.Bridge.MinimalismOblExtraction

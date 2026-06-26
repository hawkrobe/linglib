import Linglib.Fragments.Mayan.Mam.ExtractionMorphology
import Linglib.Fragments.Mayan.Mam.VoiceSystem
import Linglib.Fragments.Mayan.Kiche.ExtractionMorphology
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Agree
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Morphology.DM.VocabSimple
import Linglib.Studies.Scott2023

/-!
# Oblique Extraction in Mayan
[elkins-torrence-brown-2026] [mendes-ranero-2021] [imanishi-2020]

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
| FPG (matrix wi ↔ embedded comp) | Does not hold    | Holds                 |
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

namespace ElkinsTorrenceBrown2026

-- ============================================================================
-- Part I: Cross-Linguistic Comparison
-- ============================================================================

open Mam Kiche

-- ============================================================================
-- § 1: Shared Properties
-- ============================================================================

/-- Both Mam and K'ichean use dedicated morphemes for oblique extraction. -/
theorem both_mark_oblique :
    mamExtractionProfile.strategy = .dedicatedMorpheme ∧
    kicheanExtractionProfile.strategy = .dedicatedMorpheme := ⟨rfl, rfl⟩

/-- Both exempt temporal obliques from extraction marking. -/
theorem both_exempt_temporal :
    (Mam.temporalOblExtraction.isTemporal = true ∧
     Mam.temporalOblExtraction.judgment = .blocked) ∧
    Kiche.temporalOblExtraction.wiLicensed = false :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- Neither marks subject extraction (Agent Focus instead). -/
theorem neither_marks_subject :
    transSubjExtraction.judgment = .blocked ∧
    Kiche.subjectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Neither marks object extraction. -/
theorem neither_marks_object :
    transObjExtraction.judgment = .blocked ∧
    Kiche.objectExtraction.wiLicensed = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: Parametric Differences
-- ============================================================================

/-- KEY CONTRAST — Reason obliques ('why'):
    Mam =(y)a' IS licensed with reason extraction; K'ichean *wi* is NOT. -/
theorem reason_oblique_contrast :
    transOblExtraction.judgment = .licensed ∧
    Kiche.reasonOblExtraction.wiLicensed = false := ⟨rfl, rfl⟩

/-- Mam =(y)a' is conditioned by clause size (Voice must project);
    K'ichean *wi* is conditioned by complementizer presence (FPG). -/
theorem clause_size_sensitivity :
    MamClauseType.fullCP.projectsVoice = true ∧
    MamClauseType.aspectless.projectsVoice = true ∧
    MamClauseType.infinitival.projectsVoice = false := ⟨rfl, rfl, rfl⟩

/-- The FPG holds for K'ichean: matrix *wi* tracks overt complementizer. -/
theorem kichean_fpg_holds :
    Kiche.ldData.all (λ d =>
      d.embeddedType.hasComp == d.wiOnMatrix) = true := by
  decide

-- ============================================================================
-- § 3: Theoretical Implications
-- ============================================================================

/-- Genuinely different mechanisms producing superficially similar patterns. -/
inductive ExtractionMorphologyMechanism where
  | agreeReflex     -- Morpheme on probe head (Mam =(y)a')
  | copySpellout    -- Morpheme at extraction site (K'ichean *wi*)
  deriving DecidableEq, Repr

def mamMechanism : ExtractionMorphologyMechanism := .agreeReflex
def kicheanMechanism : ExtractionMorphologyMechanism := .copySpellout

theorem different_mechanisms :
    mamMechanism ≠ kicheanMechanism := by decide

-- ============================================================================
-- Part II: Minimalist Analysis
-- ============================================================================

open Minimalist

/-! ### Mam Voice substrate (Minimalist)

This subsection houses the Minimalist `VoiceHead`, `ClauseSpine`, and
`MamDirHead` definitions for Mam, formerly in
`Linglib/Fragments/Mayan/Mam/VoiceSystem.lean`. Per CLAUDE.md
"Per-language paper-specific apparatus lives in Studies, not
Fragments," these belong with the paper that anchors them
([elkins-torrence-brown-2026] for the =(y)a' analysis;
[scott-2023] for the antipassive). The Fragment file retains only
the theory-neutral `mamVoiceSystem : VoiceSystemProfile`.

`Studies/Scott2023.lean` consumes `mamVoice` and
`eqYaVocab` from this file via cross-Studies import. -/

/-- Mam agentive Voice head with [uOblique] probe.

    In Mam, Voice⁰ probes for an oblique feature on a passing
    Ā-moved constituent. When an oblique DP moves through Spec,VoiceP,
    Agree values [uOblique] as [+oblique], which is then spelled out
    as =(y)a' at PF. -/
def mamVoice : VoiceHead :=
  { flavor := .agentive
  , hasD := true
  , features := .ofGramFeatures [.unvalued (.oblique false)] }

/-- Mam transitive clause spine: full CP with Voice. -/
def mamTransitiveSpine : ClauseSpine := ClauseSpine.cP

/-- Mam aspectless complement spine: VoiceP-sized.
    Still has Voice → =(y)a' possible. -/
def mamAspectlessSpine : ClauseSpine := ClauseSpine.voiceP

/-- Mam infinitival complement spine: VP-sized.
    No Voice → =(y)a' impossible. -/
def mamInfinitivalSpine : ClauseSpine := ClauseSpine.bareVP

/-- Mam directional auxiliary head (Dir⁰).

    Dir is NOT a universal category — it is specific to Mayan languages.
    Modeled as a language-specific type rather than added to `Cat`.
    In Elkins et al.'s analysis, Dir⁰ occupies V1 position in the verbal
    template (Voice > V1(Dir) > Appl > V2(root)). Like Voice⁰, Dir⁰
    bears [uOblique] and can host =(y)a'. -/
structure MamDirHead where
  /-- Cislocative (toward speaker) vs translocative (away). -/
  cislocative : Bool
  /-- Whether this Dir head carries [uOblique]. -/
  hasUOblique : Bool := false
  deriving DecidableEq, Repr

/-- Dir⁰'s probe features when it carries [uOblique]. -/
def MamDirHead.features (d : MamDirHead) : FeatureBundle :=
  if d.hasUOblique then .ofGramFeatures [.unvalued (.oblique false)] else ⊥

/-- Cislocative directional with [uOblique]. -/
def dirCis : MamDirHead := { cislocative := true, hasUOblique := true }

/-- Translocative directional with [uOblique]. -/
def dirTrans : MamDirHead := { cislocative := false, hasUOblique := true }

/-- Vocabulary entry for =(y)a': maps [+oblique] on Voice⁰ to "=(y)a'". -/
def eqYaVocab : VocabEntry :=
  { features := .ofGramFeatures [.valued (.oblique true)]
  , exponent := "=(y)a'"
  , context := some .Voice }

/-- The Mam Voice vocabulary: just the =(y)a' entry. -/
def mamVoiceVocab : Vocabulary := [eqYaVocab]

/-- Mam passive Voice head: carries [uOblique] just like agentive Voice.
    [elkins-torrence-brown-2026] §7.2: =(y)a' co-occurs with
    passive *-njtz*. -/
def mamPassiveVoice : VoiceHead :=
  { flavor := .nonThematic
  , hasD := false
  , features := .ofGramFeatures [.unvalued (.oblique false)] }

/-- Mam antipassive Voice head ([scott-2023] §2.5.4.1).
    Subject gets ABS not ERG; not a phase head. -/
def mamAntipassiveVoice : VoiceHead :=
  { flavor := .antipassive
  , hasD := true
  , features := ⊥ }

-- ── Substrate-level theorems ─────────────────────────────────────────

/-- Mam Voice head carries [uOblique]. -/
theorem mamVoice_has_uOblique :
    hasUnvaluedFeature mamVoice.features (.oblique false) = true := by decide

/-- Mam Voice is a phase head. -/
theorem mamVoice_is_phase : mamVoice.IsPhasal := by decide

/-- Mam Voice assigns a θ-role (agentive). -/
theorem mamVoice_assigns_theta : mamVoice.AssignsTheta := by decide

/-- Mam transitive spine projects Voice. -/
theorem mamTransitive_has_voice :
    mamTransitiveSpine.projects .Voice = true := by decide

/-- Mam aspectless spine projects Voice. -/
theorem mamAspectless_has_voice :
    mamAspectlessSpine.projects .Voice = true := by decide

/-- Mam infinitival spine does NOT project Voice. -/
theorem mamInfinitival_lacks_voice :
    mamInfinitivalSpine.projects .Voice = false := by decide

/-- Cislocative Dir carries [uOblique]. -/
theorem dirCis_has_uOblique : dirCis.hasUOblique = true := rfl

/-- Translocative Dir carries [uOblique]. -/
theorem dirTrans_has_uOblique : dirTrans.hasUOblique = true := rfl

/-- Dir's probe features match Voice's. -/
theorem dir_features_match_voice :
    dirCis.features = mamVoice.features := by decide

/-- Passive and agentive Voice differ in flavor but share the same
    oblique probe features. -/
theorem passive_voice_same_features :
    mamPassiveVoice.features = mamVoice.features ∧
    mamPassiveVoice.flavor ≠ mamVoice.flavor := ⟨rfl, by decide⟩

/-- Antipassive Voice assigns a θ-role (the agent is present). -/
theorem mamAntipassive_assigns_theta :
    mamAntipassiveVoice.AssignsTheta := by decide

/-- Antipassive Voice is NOT a phase head. -/
theorem mamAntipassive_not_phase :
    ¬ mamAntipassiveVoice.IsPhasal := by decide

/-- Antipassive and agentive Voice differ in phase-head status but both
    assign θ-roles. -/
theorem antipassive_vs_agentive :
    (mamAntipassiveVoice.AssignsTheta ↔ mamVoice.AssignsTheta) ∧
    (mamAntipassiveVoice.IsPhasal ↔ ¬ mamVoice.IsPhasal) := by decide

-- ============================================================================
-- § 4: Spellout Theorems
-- ============================================================================

/-- Valued [+oblique] on Voice spells out as =(y)a'. -/
theorem spellout_oblique_voice :
    spellout mamVoiceVocab (.ofGramFeatures [.valued (.oblique true)]) (some .Voice) = some "=(y)a'" := by
  decide

/-- Without [+oblique], Voice has no exponent from this vocabulary. -/
theorem spellout_no_oblique :
    spellout mamVoiceVocab (.ofGramFeatures [.valued (.oblique false)]) (some .Voice) = none := by
  decide

/-- [+oblique] on a non-Voice head does not yield =(y)a'
    (context restriction blocks insertion). -/
theorem spellout_oblique_wrong_context :
    spellout mamVoiceVocab (.ofGramFeatures [.valued (.oblique true)]) (some .T) = none := by
  decide

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
  exact ⟨by decide, by decide, rfl⟩

/-- Transitive + subject extraction → no =(y)a'. -/
theorem bridge_trans_subj :
    predictEqYa mamTransitiveSpine false = .blocked ∧
    transSubjExtraction.judgment = .blocked := by
  exact ⟨by decide, rfl⟩

/-- Transitive + object extraction → no =(y)a'. -/
theorem bridge_trans_obj :
    predictEqYa mamTransitiveSpine false = .blocked ∧
    transObjExtraction.judgment = .blocked := by
  exact ⟨by decide, rfl⟩

/-- Passive + oblique → =(y)a' licensed. -/
theorem bridge_passive_obl :
    mamTransitiveSpine.projects .Voice = true ∧
    predictEqYa mamTransitiveSpine true = .licensed ∧
    passiveOblExtraction.judgment = .licensed := by
  exact ⟨by decide, by decide, rfl⟩

/-- Temporal oblique + full clause → =(y)a' BLOCKED. -/
theorem bridge_temporal_obl :
    predictEqYa mamTransitiveSpine true (isTemporal := true) = .blocked ∧
    temporalOblExtraction.judgment = .blocked := by
  exact ⟨by decide, rfl⟩

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
  exact ⟨by decide, rfl, rfl⟩

/-- LD from aspectless → =(y)a' licensed on both. -/
theorem bridge_ld_aspectless :
    (spineOf ldAspectless.embeddedClauseType).projects .Voice = true ∧
    ldAspectless.matrixJudgment = .licensed ∧
    ldAspectless.embeddedJudgment = .licensed := by
  exact ⟨by decide, rfl, rfl⟩

/-- LD from infinitival → =(y)a' on matrix only. -/
theorem bridge_ld_infinitival :
    (spineOf ldInfinitival.embeddedClauseType).projects .Voice = false ∧
    ldInfinitival.matrixJudgment = .licensed ∧
    ldInfinitival.embeddedJudgment = .blocked := by
  exact ⟨by decide, rfl, rfl⟩

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
  decide

/-- All LD embedded predictions match. -/
theorem all_ld_embedded_predictions_match :
    ldData.all (λ d =>
      d.embeddedClauseType.projectsVoice == (d.embeddedJudgment == .licensed)) = true := by
  decide

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
  exact ⟨by decide, by decide, rfl, rfl⟩

-- ============================================================================
-- § 10: ClauseSpine vs. ComplementSize
-- ============================================================================

/-- ClauseSpine is finer than ComplementSize: it can distinguish
    infinitival (VP) from aspectless (VoiceP). -/
theorem clauseSpine_finer_than_complementSize :
    mamAspectlessSpine.projects .Voice = true ∧
    mamInfinitivalSpine.projects .Voice = false := by
  exact ⟨by decide, by decide⟩

-- ============================================================================
-- § 11: Dir⁰ Spellout
-- ============================================================================

/-- Dir⁰ also carries [uOblique]. -/
theorem dir_probe_matches_voice :
    dirCis.features = mamVoice.features := by decide

/-- Dir⁰ with valued [+oblique] also spells out as =(y)a'. -/
theorem dir_spellout_eqya :
    spellout mamVoiceVocab (.ofGramFeatures [.valued (.oblique true)]) (some .Voice) = some "=(y)a'" := by
  decide

-- ============================================================================
-- § 12: Derivation Tree
-- ============================================================================

section Derivation

open RootedTree

/-- Leaf tokens for the SJO Mam transitive-CP derivation. -/
private def obliqueTok : LIToken := ⟨.simple .D [] "jawu'", 1⟩
private def verbTok    : LIToken := ⟨.simple .V [.D] "loq'", 2⟩
private def objectTok  : LIToken := ⟨.simple .D [] "wääy", 3⟩
private def voiceTok   : LIToken := ⟨.simple .Voice [.V] "", 4⟩
private def tTok       : LIToken := ⟨.simple .T [.Voice] "", 5⟩
private def cTok       : LIToken := ⟨.simple .C [.T] "", 6⟩

/-- The full CP derivation, built planar-first (Merge `SO.node` is noncomputable,
    so concrete `decide`-able trees use the planar DSL): the oblique DP undergoes
    successive-cyclic Ā-movement, surfacing at Spec,CP with a trace lower down.
    Structure: `[CP oblique [C' C [TP T [VoiceP oblique [Voice' Voice [VP V obj]]]]]]`. -/
private def cp : SO :=
  SO.ofPlanar
    (SO.nodeP (SO.leafP obliqueTok)
      (SO.nodeP (SO.leafP cTok)
        (SO.nodeP (SO.leafP tTok)
          (SO.nodeP (SO.leafP obliqueTok)
            (SO.nodeP (SO.leafP voiceTok)
              (SO.nodeP (SO.leafP verbTok) (SO.leafP objectTok)))))))

theorem derivation_tree_size : cp.nodeCount = 6 := by decide

theorem voice_has_uOblique :
    hasUnvaluedFeature mamVoice.features (.oblique false) = true := by
  decide

private def oblique_goal_features : FeatureBundle := .ofGramFeatures [.valued (.oblique true)]

/-- Agree at Voice: [uOblique] valued by oblique DP's [+oblique]. -/
theorem voice_agree_values_oblique :
    applyAgree mamVoice.features oblique_goal_features (.oblique false) =
    some (.ofGramFeatures [.valued (.oblique true)]) := by
  decide

/-- Spellout: valued [+oblique] on Voice maps to "=(y)a'". -/
theorem voice_spellout_eqya :
    spellout mamVoiceVocab (.ofGramFeatures [.valued (.oblique true)]) (some .Voice) =
    some "=(y)a'" := by
  decide

/-- Full derivation pipeline: Agree then Spellout → "=(y)a'". -/
theorem full_derivation_pipeline :
    (applyAgree mamVoice.features oblique_goal_features (.oblique false)).bind
      (λ fb => spellout mamVoiceVocab fb (some .Voice)) = some "=(y)a'" := by
  decide

end Derivation

-- ============================================================================
-- § 13: Unified Agree — Ā-agreement and φ-agreement as One Operation
-- (back-reference to [scott-2023]; this lives in ETB 2026 because
--  the cross-paper bridge runs from later → earlier per CLAUDE.md
--  chronological-dependency rule.)
-- ============================================================================

/-! Voice⁰ in Mam carries two independent probes:

1. **φ-probe** [uPerson, uNumber] (analyzed by [scott-2023]):
   Agrees with agent in Spec,VoiceP, yielding Set A morphology.
2. **Oblique probe** [uOblique] (analyzed by [elkins-torrence-brown-2026],
   this file): Agrees with a passing Ā-moved oblique, yielding =(y)a'
   on Voice⁰.

Both are instances of the same abstract Agree operation: probe searches
c-command domain, finds closest matching goal, copies features, and the
valued features are spelled out by Vocabulary Insertion. They differ only
in which features they probe for and what vocabulary entries match. -/

section UnifiedAgree
open Scott2023

/-- Voice's oblique probe features (paired with Scott 2023's φ-probe). -/
private def voiceOblProbe : FeatureBundle := mamVoice.features

/-- Both Voice probes are unvalued features. -/
theorem both_probes_unvalued :
    (Minimalist.FeatureBundle.toGramFeatures voiceProbe).all GramFeature.isUnvalued = true ∧
    (Minimalist.FeatureBundle.toGramFeatures voiceOblProbe).all GramFeature.isUnvalued = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- φ-Agree (Scott 2023) and oblique-Agree (this paper) are parallel
    instances of the same operation, differing only in which features
    are probed and which vocabulary entries match. -/
theorem phi_and_oblique_agree_parallel :
    -- φ-Agree pipeline: value person, then number, then spellout
    (applyAgree voiceProbe dp3sg (.phi (.person .third))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number .singular))) = some voiceFullyAgreed ∧
    spellout setAVocab voiceFullyAgreed (some .v) = some "t-" ∧
    -- Oblique-Agree pipeline: value oblique, then spellout
    applyAgree voiceOblProbe (.ofGramFeatures [.valued (.oblique true)]) (.oblique false) =
      some (.ofGramFeatures [.valued (.oblique true)]) ∧
    spellout [eqYaVocab] (.ofGramFeatures [.valued (.oblique true)]) (some .Voice) = some "=(y)a'" := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end UnifiedAgree

end ElkinsTorrenceBrown2026

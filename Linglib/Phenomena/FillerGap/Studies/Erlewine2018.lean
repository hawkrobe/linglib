import Linglib.Fragments.TobaBatak.Basic
import Linglib.Fragments.TobaBatak.Relativization
import Linglib.Core.Relativization.Extraction
import Linglib.Theories.Syntax.Minimalism.Position
import Linglib.Theories.Syntax.Minimalism.Derivation
import Linglib.Phenomena.WordOrder.Studies.ColeHermon2008

/-!
# Toba Batak Extraction Restriction @cite{erlewine-2018}
@cite{elkins-torrence-brown-2026}

Empirical data on the extraction restriction in Toba Batak (only the
pivot can undergo Ā-movement) plus @cite{erlewine-2018}'s Minimalist
analysis (predicate fronting + nominal licensing).

## Key Empirical Findings

1. **Pivot-only extraction**: Only the pivot argument can be Ā-extracted.
2. **Voice determines pivot**: Actor Voice → agent is pivot; Object Voice
   → patient is pivot.
3. **Voice symmetry**: AV makes the agent extractable but not the patient;
   OV makes the patient extractable but not the agent.
4. **Long-distance extraction**: The extracted element must be the pivot
   of the most deeply embedded clause.

## The Analysis

The extraction restriction follows from the interaction of probing and
nominal licensing:

1. **Predicate fronting**: C bears `[PROBE:FOC]`, attracting the closest
   `[+FOC]` constituent — normally the vP — to Spec,CP, deriving V-initial
   word order. The subject/pivot is stranded in Spec,TP after vP fronts.

2. **Nominal licensing**: T bears `[PROBE:D]`, which Case-licenses the
   subject DP in Spec,TP. If a non-subject DP were attracted to Spec,CP
   by `[PROBE:FOC]`, it would end up in a position with no available
   Case licensor — the derivation crashes. Therefore only the pivot
   (already Case-licensed by T) can be Ā-extracted.

3. **Non-DP extraction is unrestricted**: Since the restriction is about
   nominal licensing, non-DP constituents (adverbs, PPs) can freely
   front to Spec,CP regardless of voice.

The descriptive generalization: extraction of a DP argument is grammatical
iff it is the pivot for the given voice.

## Cross-Linguistic Context

Toba Batak's extraction restriction contrasts with:
- **Tagalog/Seediq**: Philippine-style voice/Case determines extraction
  via agreement morphology — a voice-as-case system. @cite{erlewine-2018}
  argues TB is NOT this type.
- **Mam** (Mayan): Extraction is unrestricted, but oblique extraction
  triggers a dedicated morpheme as an Agree reflex on Voice⁰
  (see @cite{elkins-torrence-brown-2026}).

## Connection to Mam

Both TB and Mam involve successive-cyclic movement leaving morphological
traces at clause boundaries. The shared abstraction is `CyclicChain` from
Position.lean:

- **Mam**: Each intermediate Voice⁰ Agrees [+oblique], spelling out as a
  dedicated morpheme. The chain entries correspond to feature-valuation
  events.
- **TB**: Each intermediate C⁰ shows extraction voice morphology,
  reflecting the passage of the wh-element through Spec,CP.

-/

namespace Phenomena.FillerGap.Studies.Erlewine2018

open Fragments.TobaBatak
open ColeHermon2008 (v_mangatuk n_biangi n_dakdanakan vp tobaBatakVOS)
open Minimalism

-- ============================================================================
-- § 1: Empirical Data Verification
-- ============================================================================

theorem extraction_data_count : extractionData.length = 8 := by decide

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

/-- AV + adjunct: grammatical (adjuncts don't need Case). -/
theorem av_adjunct_grammatical :
    avAdjunctExtraction.judgment = .grammatical := rfl

/-- OV + adjunct: grammatical (adjuncts don't need Case). -/
theorem ov_adjunct_grammatical :
    ovAdjunctExtraction.judgment = .grammatical := rfl

-- ============================================================================
-- § 2: Descriptive Generalizations
-- ============================================================================

/-- For DP arguments: extraction is grammatical iff the extracted element
    is the pivot for the given voice. -/
theorem dp_extraction_iff_pivot :
    extractionData.all (λ d =>
      match d.extracted with
      | .dpArg _ => d.extractsPivot == (d.judgment == .grammatical)
      | .adjunct => true) = true := by
  decide

/-- For non-DP adjuncts: extraction is always grammatical regardless of
    voice, because adjuncts don't need Case licensing. -/
theorem adjunct_always_grammatical :
    extractionData.all (λ d =>
      match d.extracted with
      | .adjunct => d.judgment == .grammatical
      | .dpArg _ => true) = true := by
  decide

/-- Voice symmetry: AV and OV are mirror images — each makes exactly one
    argument extractable (the pivot) and blocks all others. -/
theorem voice_symmetry :
    avAgentExtraction.judgment = .grammatical ∧
    ovPatientExtraction.judgment = .grammatical ∧
    avPatientExtraction.judgment = .ungrammatical ∧
    ovAgentExtraction.judgment = .ungrammatical := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Cross-Linguistic Profile
-- ============================================================================

/-- TB uses structural restriction, not dedicated morpheme or voice
    alternation in the Tagalog sense. -/
theorem tb_strategy :
    tbExtractionProfile.strategy = .structuralRestriction := rfl

/-- TB distinguishes extracted positions via voice (which role is pivot). -/
theorem tb_distinguishes :
    tbExtractionProfile.distinguishesPosition = true := rfl

-- ============================================================================
-- § 4: Data → Profile → AH Chain
-- ============================================================================

/-! Connects three independent data sources through the AH bridge:
1. Individual extraction datums (from @cite{erlewine-2018})
2. The ExtractionProfile summary (markedPositions)
3. RelClauseMarkers (from @cite{keenan-comrie-1977})

If any link is wrong — e.g., listing `.directObject` as extractable when
relativization markers don't cover DO — the chain breaks.

Note: the extraction data uses `ArgumentRole` (agent, patient) while the
ExtractionProfile and AH use `ExtractionTarget` (subject, directObject).
Voice promotion means the patient's *default* position is DO, but its
*surface* extraction position is always subject (the pivot). -/

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
  decide

/-- Link 2→3: Every extractable position (ExtractionTarget) maps to an AH
    position that is covered by some Toba Batak relativization marker. -/
theorem extractable_positions_are_relativizable :
    tbExtractionProfile.markedPositions.all (λ et =>
      let ahPos := Core.extractionTargetToAH et
      relMarkers.any (·.covers ahPos)) = true := by
  decide

/-- Full chain (all three links as a single conjunction). -/
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
  decide

-- ============================================================================
-- § 5: Erlewine's Prediction Function
-- ============================================================================

/-- Predict whether extraction is grammatical from voice + extractee.

    The nominal licensing analysis predicts:
    - DP arguments: extraction is grammatical iff the DP is the pivot,
      because only the pivot is Case-licensed (by T's [PROBE:D] in
      Spec,TP) before Ā-extraction.
    - Non-DP adjuncts: always grammatical, because adjuncts don't need
      Case licensing. -/
def predictExtraction (voice : Fragments.TobaBatak.Voice) (extractee : Interfaces.Extractee) :
    ExtractionJudgment :=
  match extractee with
  | .adjunct => .grammatical
  | .dpArg role =>
    if role == voice.pivotRole then .grammatical else .ungrammatical

-- ============================================================================
-- § 6: Per-Datum Bridge Theorems
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

/-- AV + adjunct: no Case needed → freely extractable. -/
theorem bridge_av_adjunct :
    predictExtraction .av .adjunct = .grammatical ∧
    avAdjunctExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

/-- OV + adjunct: no Case needed → freely extractable. -/
theorem bridge_ov_adjunct :
    predictExtraction .ov .adjunct = .grammatical ∧
    ovAdjunctExtraction.judgment = .grammatical := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Completeness
-- ============================================================================

/-- The structural analysis correctly predicts every monoclausal datum. -/
theorem all_predictions_match :
    extractionData.all (λ d =>
      predictExtraction d.voice d.extracted == d.judgment) = true := by
  decide

/-- For DP arguments, the prediction function agrees with extractsPivot. -/
theorem prediction_matches_pivot :
    extractionData.all (λ d =>
      match d.extracted with
      | .dpArg _ =>
        (predictExtraction d.voice d.extracted == .grammatical)
          == d.extractsPivot
      | .adjunct => true) = true := by
  decide

-- ============================================================================
-- § 8: Structural Grounding
-- ============================================================================

/-- For DP arguments, the prediction function IS the pivot check — they
    agree extensionally on the extraction data. -/
theorem structural_grounding :
    extractionData.all (λ d =>
      match d.extracted with
      | .dpArg _ =>
        predictExtraction d.voice d.extracted ==
          if d.extractsPivot then .grammatical else .ungrammatical
      | .adjunct => true) = true := by
  decide

/-- The nominal licensing analysis predicts non-DPs extract freely. -/
theorem nonDP_unrestricted :
    ∀ v : Fragments.TobaBatak.Voice,
      predictExtraction v .adjunct = .grammatical := by
  intro v; rfl

-- ============================================================================
-- § 9: Cross-Austronesian Bridge — @cite{cole-hermon-2008}
-- ============================================================================

/-- VP-raising (@cite{cole-hermon-2008}, Toba Batak) and predicate
    fronting (@cite{erlewine-2018}, Toba Batak) share the same core
    prediction: the predicate phrase moves above the subject, yielding
    V-initial surface order.

    Both analyses predict:
    1. The predicate c-commands the subject at surface structure
    2. Only the subject (pivot) can subsequently Ā-extract
    3. Non-DP adjuncts extract freely (not subject to Case licensing)

    The key parametric difference:
    - @cite{cole-hermon-2008}: VP moves to Spec,TP; subject stranded in Spec,vP
    - @cite{erlewine-2018}: vP moves to Spec,CP; subject stranded in Spec,TP -/
theorem predicate_fronting_yields_vi_order :
    ColeHermon2008.tobaBatakVOS.final.phonYield.head?
      = some "mangatuk" := by decide

-- ============================================================================
-- § 10: vP-to-Spec,CP Derivation
-- ============================================================================

/-! ## vP-to-Spec,CP analysis

@cite{erlewine-2018}'s analysis differs structurally from @cite{cole-hermon-2008}:
- @cite{cole-hermon-2008}: VP → Spec,TP
- Erlewine: Subj → Spec,TP **then** vP → Spec,CP

Both derive the same VOS surface order, but the derived tree is
structurally different: Erlewine's has an additional CP layer, and the
fronted constituent is vP (containing a subject trace) rather than bare
VP. -/

/-- Little v (Erlewine's analysis, unique ID). -/
def v_head_e := mkLeaf .v [.V] 101

/-- T head (Erlewine's analysis, unique ID). -/
def t_head_e := mkLeaf .T [.v] 102

/-- C head bearing [PROBE:FOC] (Erlewine's analysis, unique ID). -/
def c_head_e := mkLeaf .C [.T] 103

/-- The vP after subject extraction: `[vP tSubj [v' v [VP V Obj]]]`.

    The trace marks where the subject DP originated before moving to
    Spec,TP. -/
def vP_traced : SyntacticObject := .node (mkTrace 0) (.node v_head_e vp)

/-- Erlewine's vP-to-Spec,CP derivation for Toba Batak VOS.

    Steps (bottom-up):
    1. EM-R Obj  → `[VP V Obj]`
    2. EM-L v    → `[v' v VP]`
    3. EM-L Subj → `[vP Subj [v' v VP]]`
    4. EM-L T    → `[TP T [vP Subj [v' v VP]]]`
    5. IM Subj   → `[TP Subj [T' T [vP tSubj [v' v VP]]]]`
    6. EM-L C    → `[CP C [TP Subj [T' T [vP tSubj [v' v VP]]]]]`
    7. IM vP     → `[CP [vP tSubj v VP] [C' C [TP Subj [T' T tvP]]]]` -/
def erlewineDerivation : Derivation :=
  { initial := v_mangatuk
    steps := [
      .emR n_biangi,
      .emL v_head_e,
      .emL n_dakdanakan,
      .emL t_head_e,
      .im n_dakdanakan 0,
      .emL c_head_e,
      .im vP_traced 1
    ] }

/-- Erlewine's derivation yields VOS word order. -/
theorem erlewine_yields_vos :
    erlewineDerivation.final.phonYield = ["mangatuk", "biangi", "dakdanakan"] := by
  decide

/-- Both analyses agree on VOS surface order despite different structural heights. -/
theorem cole_erlewine_agree_on_order :
    tobaBatakVOS.final.phonYield = erlewineDerivation.final.phonYield := by
  decide

/-- Erlewine has TWO movements (Subj → Spec,TP + vP → Spec,CP) vs
    @cite{cole-hermon-2008}'s ONE (VP → Spec,TP). -/
theorem erlewine_two_movements :
    erlewineDerivation.movedItems.length = 2 := by decide

/-- Different derived structures despite the same word order. -/
theorem different_derived_structure :
    tobaBatakVOS.final.shape ≠ erlewineDerivation.final.shape := by decide

/-- Fronted vP c-commands the subject in Erlewine's derived tree.

    The fronted vP is in Spec,CP; its sister C' dominates the subject in
    Spec,TP. This yields the same binding prediction as
    @cite{cole-hermon-2008}'s VP-in-Spec,TP analysis: the predicate
    phrase c-commands the subject. -/
theorem vP_ccommands_subject_erlewine :
    cCommandsIn erlewineDerivation.final vP_traced n_dakdanakan := by
  have h_final : erlewineDerivation.final =
    .node vP_traced (.node c_head_e (.node n_dakdanakan (.node t_head_e (mkTrace 1)))) := by
    decide
  rw [h_final]
  exact ⟨.node c_head_e (.node n_dakdanakan (.node t_head_e (mkTrace 1))),
         ⟨_, self_mem_subtrees _, Or.inl rfl, Or.inr rfl, by decide⟩,
         Or.inr (contains.trans _ _ _ (Or.inr rfl) (contains.imm _ _ (Or.inl rfl)))⟩

/-- Same VP base in both analyses (stage after first merge). -/
theorem same_vp :
    tobaBatakVOS.stageAt 1 = erlewineDerivation.stageAt 1 := by decide

end Phenomena.FillerGap.Studies.Erlewine2018

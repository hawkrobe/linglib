import Linglib.Phenomena.FillerGap.TobaBatak
import Linglib.Theories.Syntax.Minimalism.Core.Position
import Linglib.Theories.Syntax.Minimalism.Core.Derivation
import Linglib.Phenomena.WordOrder.Studies.ColeHermon2008

/-!
# Minimalism Bridge: Toba Batak Extraction Restriction @cite{erlewine-2018}
@cite{elkins-torrence-brown-2026}

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

namespace Erlewine2018

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

-- ============================================================================
-- § 5: Cross-Austronesian Bridge — @cite{cole-hermon-2008}
-- ============================================================================

/-- VP-raising (@cite{cole-hermon-2008}, Toba Batak) and predicate fronting
    (@cite{erlewine-2018}, Toba Batak) share the same core prediction:
    the predicate phrase moves above the subject, yielding V-initial
    surface order.

    Both analyses predict:
    1. The predicate c-commands the subject at surface structure
    2. Only the subject (pivot) can subsequently Ā-extract
    3. Non-DP adjuncts extract freely (not subject to Case licensing)

    The key parametric difference:
    - @cite{cole-hermon-2008}: VP moves to Spec,TP; subject stranded in Spec,vP
    - @cite{erlewine-2018}: vP moves to Spec,CP; subject stranded in Spec,TP -/
theorem predicate_fronting_yields_vi_order :
    ColeHermon2008.tobaBatakVOS.final.phonYield.head?
      = some "mangatuk" := by native_decide

-- ============================================================================
-- § 6: vP-to-Spec,CP Derivation — @cite{erlewine-2018} §4.2
-- ============================================================================

/-! ## vP-to-Spec,CP analysis

@cite{erlewine-2018}'s analysis differs structurally from @cite{cole-hermon-2008}:
- @cite{cole-hermon-2008}: VP → Spec,TP (5 steps: 4 EM + 1 IM)
- Erlewine: Subj → Spec,TP **then** vP → Spec,CP (7 steps: 5 EM + 2 IM)

Both derive the same VOS surface order, but the derived tree is structurally
different: Erlewine's has an additional CP layer, and the fronted constituent
is vP (containing a subject trace) rather than bare VP. -/

open ColeHermon2008 (v_mangatuk n_biangi n_dakdanakan vp tobaBatakVOS)
open Minimalism

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
      .emR n_biangi,        -- [VP V Obj]
      .emL v_head_e,        -- [v' v VP]
      .emL n_dakdanakan,    -- [vP Subj [v' v VP]]
      .emL t_head_e,        -- [TP T [vP Subj [v' v VP]]]
      .im n_dakdanakan 0,   -- [TP Subj [T' T [vP tSubj [v' v VP]]]]
      .emL c_head_e,        -- [CP C [TP Subj [T' T [vP tSubj [v' v VP]]]]]
      .im vP_traced 1       -- [CP [vP tSubj v VP] [C' C [TP Subj [T' T tvP]]]]
    ] }

/-- Erlewine's derivation yields VOS word order. -/
theorem erlewine_yields_vos :
    erlewineDerivation.final.phonYield = ["mangatuk", "biangi", "dakdanakan"] := by
  native_decide

/-- Both analyses agree on VOS surface order despite different structural heights. -/
theorem cole_erlewine_agree_on_order :
    tobaBatakVOS.final.phonYield = erlewineDerivation.final.phonYield := by
  native_decide

/-- Erlewine has TWO movements (Subj → Spec,TP + vP → Spec,CP) vs
    @cite{cole-hermon-2008}'s ONE (VP → Spec,TP). -/
theorem erlewine_two_movements :
    erlewineDerivation.movedItems.length = 2 := by native_decide

/-- Different derived structures despite the same word order. -/
theorem different_derived_structure :
    tobaBatakVOS.final.shape ≠ erlewineDerivation.final.shape := by decide

/-- Fronted vP c-commands the subject in Erlewine's derived tree.

    The fronted vP is in Spec,CP; its sister C' dominates the subject in
    Spec,TP. This yields the same binding prediction as @cite{cole-hermon-2008}'s
    VP-in-Spec,TP analysis: the predicate phrase c-commands the subject. -/
theorem vP_ccommands_subject_erlewine :
    cCommandsIn erlewineDerivation.final vP_traced n_dakdanakan := by
  -- Compute the final tree: [CP [vP tSubj v VP] [C' C [TP Subj [T' T tvP]]]]
  have h_final : erlewineDerivation.final =
    .node vP_traced (.node c_head_e (.node n_dakdanakan (.node t_head_e (mkTrace 1)))) := by
    native_decide
  rw [h_final]
  -- vP_traced's sister is C', which dominates n_dakdanakan
  exact ⟨.node c_head_e (.node n_dakdanakan (.node t_head_e (mkTrace 1))),
         ⟨_, self_mem_subtrees _, Or.inl rfl, Or.inr rfl, by decide⟩,
         Or.inr (contains.trans _ _ _ (Or.inr rfl) (contains.imm _ _ (Or.inl rfl)))⟩

/-- Same VP base in both analyses (stage after first merge). -/
theorem same_vp :
    tobaBatakVOS.stageAt 1 = erlewineDerivation.stageAt 1 := by native_decide

end Erlewine2018

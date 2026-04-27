import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Theories.Syntax.Minimalist.Derivation
import Linglib.Theories.Syntax.Minimalist.Position
import Linglib.Fragments.TobaBatak.Basic

/-!
# VP Raising in a VOS Language @cite{cole-hermon-2008}

@cite{cole-hermon-2008} argue that VOS word order in Toba Batak derives
from VP-raising to Spec,TP (or more precisely, VoiceP-raising to Spec,FP
in their full analysis), rather than from rightward subject shift or
base-generation. Three lines of evidence converge:

1. **Word order**: VOS and the positions of IOs and adverbials follow from
   VP/VoiceP raising + remnant movement. The subject is stranded below
   the fronted predicate.

2. **Extraction restrictions**: Direct objects and passive agents cannot
   be Ā-extracted (frozen inside the raised VoiceP), while subjects,
   indirect objects, and adverbials can (they escape VoiceP before it
   raises). This freezing effect is the paper's central novel prediction.

3. **Binding asymmetries**: In actives, the subject c-commands the direct
   object (can bind a reflexive DO) but the DO cannot c-command the
   subject (cannot bind a reflexive subject). In passives, reconstruction
   allows the passive agent to bind a reflexive passive subject — a
   pattern unexplained by a purely thematic hierarchy.

## Simplification

The derivation here follows the simplified tree (2) from p. 146 of the
paper, where VP raises to Spec,TP. The paper's full analysis (§4,
trees 50–65) uses VoiceP raising to Spec,FP with remnant movement
(IO/Adv escape before VoiceP fronts), a Voice head for *mang-*/*di-*
morphology, and a richer functional sequence. The simplified derivation
suffices for the word-order and c-command predictions; the extraction
and binding predictions are formalized separately using the paper's
empirical generalizations.
-/

namespace Minimalist

/-! ## EPP Parameter (formerly `Core/EPP.lean`)

The Extended Projection Principle (EPP) requires Spec,TP to be filled.
Cross-linguistically, languages differ in *how* this requirement is
satisfied, yielding different basic word orders from the same
underlying vP-internal structure. This is the parameter space
@cite{cole-hermon-2008} exploit. -/

/-- What satisfies the EPP (requirement to fill Spec,TP). -/
inductive EPPStrategy where
  /-- Subject DP raises to Spec,TP (English, French, etc.). -/
  | subjectRaising
  /-- VP/predicate phrase raises to Spec,TP (Toba Batak VOS, Malagasy VOS). -/
  | vpRaising
  /-- Expletive inserted in Spec,TP (English *there*, French *il*). -/
  | expletive
  /-- No EPP — verb-initial order persists (one analysis of Irish/Arabic VSO). -/
  | none
  deriving Repr, DecidableEq

/-- Word-order parameter: EPP strategy and predicted basic order. -/
structure WordOrderParameter where
  language : String
  eppStrategy : EPPStrategy
  predictedOrder : String

def english_wo : WordOrderParameter :=
  { language := "English", eppStrategy := .subjectRaising, predictedOrder := "SVO" }

def tobaBatak_wo : WordOrderParameter :=
  { language := "Toba Batak", eppStrategy := .vpRaising, predictedOrder := "VOS" }

end Minimalist

namespace ColeHermon2008

open Minimalist

-- ============================================================================
-- § 1: Toba Batak Lexical Items
-- ============================================================================

/-- "mangatuk" — ACT-hit (active voice transitive verb). -/
def v_mangatuk := mkLeafPhon .V [] "mangatuk" 1

/-- "biangi" — dog-DEF (definite object DP). -/
def n_biangi := mkLeafPhon .N [] "biangi" 2

/-- "dakdanakan" — child-that (subject DP). -/
def n_dakdanakan := mkLeafPhon .N [] "dakdanakan" 3

/-- Little v (silent, selects VP). -/
def v_head := mkLeaf .v [.V] 4

/-- T (silent, selects vP). -/
def t_head := mkLeaf .T [.v] 5

/-- The VP constituent `[VP V Obj]` — the phrase that raises. -/
def vp : SyntacticObject := .node v_mangatuk n_biangi

-- ============================================================================
-- § 2: Toba Batak VOS Derivation
-- ============================================================================

/-- Toba Batak VOS via VP-raising to Spec,TP.

    Steps (bottom-up):
    1. EM-R Obj → `[VP V Obj]`
    2. EM-L v  → `[v' v VP]`
    3. EM-L Subj → `[vP Subj [v' v VP]]`
    4. EM-L T  → `[TP T [vP Subj [v' v VP]]]`
    5. IM VP   → `[TP VP [T' T [vP Subj [v' v tVP]]]]` -/
def tobaBatakVOS : Derivation :=
  { initial := v_mangatuk
    steps := [
      .emR n_biangi,
      .emL v_head,
      .emL n_dakdanakan,
      .emL t_head,
      .im vp 0
    ] }

-- ============================================================================
-- § 3: English SVO Derivation (Comparison)
-- ============================================================================

def v_saw   := mkLeafPhon .V [] "saw" 11
def n_mary  := mkLeafPhon .N [] "Mary" 12
def n_john  := mkLeafPhon .N [] "John" 13
def v_head2 := mkLeaf .v [.V] 14
def t_head2 := mkLeaf .T [.v] 15

/-- English SVO via subject-raising to Spec,TP.

    Same base as Toba Batak, but the subject (not VP) moves to Spec,TP. -/
def englishSVO : Derivation :=
  { initial := v_saw
    steps := [
      .emR n_mary,
      .emL v_head2,
      .emL n_john,
      .emL t_head2,
      .im n_john 0
    ] }

-- ============================================================================
-- § 4: Word Order Predictions
-- ============================================================================

/-- VP-raising yields Verb-Object-Subject surface order. -/
theorem toba_batak_is_vos :
    tobaBatakVOS.final.phonYield = ["mangatuk", "biangi", "dakdanakan"] := by
  native_decide

/-- Subject-raising yields Subject-Verb-Object surface order. -/
theorem english_is_svo :
    englishSVO.final.phonYield = ["John", "saw", "Mary"] := by
  native_decide

/-- Both derivations have the same tree shape before the movement step
    (stage 4). The only parametric difference is *what* moves in step 5. -/
theorem same_base_shape :
    (tobaBatakVOS.stageAt 4).shape = (englishSVO.stageAt 4).shape := by
  native_decide

/-- Toba Batak moves the VP (one moved item). -/
theorem toba_batak_moves_vp :
    tobaBatakVOS.movedItems.length = 1 := by native_decide

/-- English moves the subject DP (one moved item). -/
theorem english_moves_subject :
    englishSVO.movedItems.length = 1 := by native_decide

-- ============================================================================
-- § 5: C-Command in the Derived Tree
-- ============================================================================

/-- After VP-raising, the VP c-commands the subject in the derived tree.

    The derived tree is `[TP [VP V Obj] [T' T [vP Subj [v' v tVP]]]]`.
    VP is the left daughter of TP; its sister T' dominates the subject.

    @cite{cole-hermon-2008} use this c-command relation to explain:
    - **Freezing**: the raised VP is a moved constituent in specifier
      position, making it an island for extraction. Elements inside VP
      (including the direct object) are frozen and cannot Ā-extract.
    - **Subject accessibility**: the subject, outside the raised VP, is
      stranded and remains accessible for further extraction.

    Note: this does NOT establish "backward binding" by the object into
    the subject. The paper explicitly shows that active DOs cannot bind
    a reflexive subject (Table 1, Type C: ill-formed for all speakers).
    VP c-commanding the subject is a *phrasal* c-command relation; it
    does not entail that the DO (properly contained within VP) individually
    c-commands the subject. -/
theorem vp_ccommands_subject :
    cCommandsIn tobaBatakVOS.final vp n_dakdanakan := by
  -- Compute the final tree: [TP [VP V Obj] [T' T [vP Subj [v' v tVP]]]]
  have h_final : tobaBatakVOS.final =
    .node vp (.node t_head (.node n_dakdanakan (.node v_head (mkTrace 0)))) := by
    native_decide
  rw [h_final]
  -- VP's sister is T', which dominates the subject
  exact ⟨.node t_head (.node n_dakdanakan (.node v_head (mkTrace 0))),
         ⟨_, self_mem_subtrees _, Or.inl rfl, Or.inr rfl, by decide⟩,
         Or.inr (contains.trans _ _ _ (Or.inr rfl) (contains.imm _ _ (Or.inl rfl)))⟩

-- ============================================================================
-- § 6: EPP Parameter
-- ============================================================================

/-- Toba Batak and English instantiate the same EPP parameter space:
    VP-raising → VOS, subject-raising → SVO. -/
theorem epp_predicts_order :
    tobaBatak_wo.eppStrategy = .vpRaising ∧
    english_wo.eppStrategy = .subjectRaising := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Extraction Restrictions (§4 of the paper)
-- ============================================================================

/-! ### Freezing under VP-raising

@cite{cole-hermon-2008} §4: the VP-raising analysis predicts extraction
restrictions via **freezing**. The raised VP/VoiceP is a moved constituent
in specifier position, making it an island (following the Sentential
Subject Constraint / Condition on Extraction Domain). The predictions:

- **Direct object**: frozen inside the raised VP → cannot Ā-extract
- **Passive agent**: frozen inside the raised VoiceP → cannot Ā-extract
- **Subject (pivot)**: stranded outside the raised VP, in Spec,FP → can extract
- **Indirect object**: escapes VP via remnant movement before VP raises → can extract
- **Adverbials**: likewise escape before VP raises → can extract

These predictions match the Toba Batak extraction data formalized in
`Fragments.TobaBatak.Basic` and verified in
`Phenomena.FillerGap.Studies.Erlewine2018`.
-/

/-- The direct object is contained within the fronted VP. In the
    VP-raising analysis, this means the DO is frozen — trapped inside
    a moved constituent — and cannot be further Ā-extracted.

    This is verified computationally: `n_biangi` is contained in `vp`. -/
theorem object_inside_fronted_vp :
    containsB vp n_biangi = true := by native_decide

/-- The subject is NOT contained within the fronted VP. It is stranded
    outside the moved constituent and remains accessible for extraction.

    This is the structural basis for the pivot-only extraction restriction:
    only the subject (= pivot) survives VP-raising in a position where
    Ā-extraction is possible. -/
theorem subject_outside_fronted_vp :
    containsB vp n_dakdanakan = false := by native_decide

/-- Extraction prediction: the VP-raising analysis predicts exactly the
    extraction pattern found in Toba Batak.

    For DP arguments in actor voice:
    - Agent (= subject/pivot, outside VP): grammatical
    - Patient (= DO, inside VP): ungrammatical

    This matches `Fragments.TobaBatak.avAgentExtraction` (grammatical)
    and `Fragments.TobaBatak.avPatientExtraction` (ungrammatical). -/
theorem extraction_matches_vp_containment :
    -- Agent is outside VP → extractable (matches AV agent = grammatical)
    containsB vp n_dakdanakan = false ∧
    Fragments.TobaBatak.avAgentExtraction.judgment = .grammatical ∧
    -- Object is inside VP → frozen (matches AV patient = ungrammatical)
    containsB vp n_biangi = true ∧
    Fragments.TobaBatak.avPatientExtraction.judgment = .ungrammatical :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Binding Asymmetries (§3.4–§5 of the paper)
-- ============================================================================

/-! ### Binding data from Table 1

@cite{cole-hermon-2008} §3.4–§5 present binding data that bear on the
choice between a c-command analysis and the Semantic Hierarchy Condition
of Schachter (1984b) and Sugamoto (1984). The key data from Table 1:

| Antecedent      | Reflexive       | Acceptability |
|-----------------|-----------------|---------------|
| Active subject  | Direct object   | Type A (fully acceptable) |
| Passive agent   | Passive subject | Type A (fully acceptable) |
| Passive subject | Passive agent   | Type B (intermediate) |
| Active DO       | Active subject  | Type C (ill-formed) |

Type A follows from c-command in the base structure (pre-movement).
Type C follows from the absence of c-command: the DO does not c-command
the subject at any derivational stage.
Type B requires **reconstruction**: the passive subject can be interpreted
in its base VP-internal position, where the passive agent c-commands it.

The VP-raising analysis correctly predicts all four types. The Semantic
Hierarchy Condition alone fails to distinguish Types B and C (it predicts
both should be ill-formed, since in both cases the patient antecedes the
agent reflexive).
-/

/-- Binding acceptability from Table 1 of @cite{cole-hermon-2008}. -/
inductive BindingAcceptability where
  /-- Type A: fully acceptable for all speakers. -/
  | fullyAcceptable
  /-- Type B: intermediate — acceptable, but not the most usual
      way to express the sentence. -/
  | intermediate
  /-- Type C: ill-formed, not acceptable for any speakers. -/
  | illFormed
  deriving Repr, DecidableEq

/-- A binding datum: which NP is the antecedent, which is the reflexive,
    in which voice, and the acceptability judgment. -/
structure BindingDatum where
  antecedentRole : String
  reflexiveRole  : String
  voice          : String
  acceptability  : BindingAcceptability
  description    : String := ""
  deriving Repr

/-- Active subject antecedes DO reflexive: Type A.
    Example: "Si-Bunga mang-ida [dirina sandiri]" (Bunga saw herself.) -/
def activeSubjectBindsDO : BindingDatum :=
  { antecedentRole := "active subject"
    reflexiveRole  := "direct object"
    voice          := "active"
    acceptability  := .fullyAcceptable
    description    := "Subject c-commands DO in base [vP Subj [v' v [VP V DO]]]" }

/-- Passive agent antecedes passive subject reflexive: Type A.
    Example: "Di-ida si-Torus dirina natoari" (Himself was seen by Torus yesterday.) -/
def passiveAgentBindsSubject : BindingDatum :=
  { antecedentRole := "passive agent"
    reflexiveRole  := "passive subject"
    voice          := "passive"
    acceptability  := .fullyAcceptable
    description    := "Agent c-commands patient in base structure; reconstruction allows binding" }

/-- Passive subject antecedes passive agent reflexive: Type B.
    Example: "Di-ida [dirina sandiri] si-John" (John was seen by himself.) -/
def passiveSubjectBindsAgent : BindingDatum :=
  { antecedentRole := "passive subject"
    reflexiveRole  := "passive agent"
    voice          := "passive"
    acceptability  := .intermediate
    description    := "Surface c-command (patient raised to Spec,FP c-commands agent in Spec,vP)" }

/-- Active DO antecedes active subject reflexive: Type C.
    Example: "*[Dirina sandiri] pa-ias-hon dakdanak-i" (*Himself cleaned the child.) -/
def activeDOBindsSubject : BindingDatum :=
  { antecedentRole := "active direct object"
    reflexiveRole  := "active subject"
    voice          := "active"
    acceptability  := .illFormed
    description    := "DO never c-commands subject: trapped inside VP at every derivational stage" }

/-- All binding data from Table 1. -/
def bindingData : List BindingDatum :=
  [activeSubjectBindsDO, passiveAgentBindsSubject,
   passiveSubjectBindsAgent, activeDOBindsSubject]

/-- Types A and B are acceptable; Type C is ill-formed. -/
theorem binding_acceptability_pattern :
    activeSubjectBindsDO.acceptability = .fullyAcceptable ∧
    passiveAgentBindsSubject.acceptability = .fullyAcceptable ∧
    passiveSubjectBindsAgent.acceptability = .intermediate ∧
    activeDOBindsSubject.acceptability = .illFormed := ⟨rfl, rfl, rfl, rfl⟩

/-- The direct object does not c-command the subject (Boolean check).

    The DO's inability to bind the subject (Type C) follows from the
    derivation: the DO is inside VP, and VP c-commands the subject
    (proved in `vp_ccommands_subject`), but the DO itself does not
    c-command the subject. C-command is not inherited by sub-constituents.

    In the derived tree `[TP [VP V DO] [T' T [vP Subj ...]]]`:
    - VP c-commands Subj ✓ (VP's sister T' dominates Subj)
    - DO does NOT c-command Subj ✗ (DO's sister is V, which does not
      dominate Subj — V is inside VP, not sister to anything outside VP)

    This asymmetry is why Types A and C differ: the subject (in Spec,vP)
    c-commands into VP (can bind a reflexive DO), but the DO (inside VP)
    cannot c-command out past VP (cannot bind a reflexive subject). -/
theorem object_does_not_ccommand_subject :
    ¬ cCommandsIn tobaBatakVOS.final n_biangi n_dakdanakan := by
  native_decide

-- ============================================================================
-- § 9: Integration Bridges
-- ============================================================================

/-! ### Connecting to Toba Batak extraction infrastructure

The VP-raising analysis's extraction predictions are independently
formalized in `Fragments.TobaBatak.Basic` (empirical extraction data)
and `Phenomena.FillerGap.Studies.Erlewine2018` (verification theorems).
This section bridges the derivational analysis to that data.
-/

/-- The EPP strategy for Toba Batak is VP-raising, which is the
    derivational mechanism that produces the freezing effect responsible
    for the extraction restriction. -/
theorem vp_raising_drives_extraction :
    tobaBatak_wo.eppStrategy = .vpRaising ∧
    Fragments.TobaBatak.tbExtractionProfile.strategy = .structuralRestriction :=
  ⟨rfl, rfl⟩

/-- The extraction profile marks only the subject position as extractable.
    This is exactly the position that VP-raising strands outside the
    fronted predicate: the pivot in Spec,TP (or Spec,FP in the full
    analysis). -/
theorem only_subject_extractable :
    Fragments.TobaBatak.tbExtractionProfile.markedPositions = [.subject] := rfl

/-- The voice system is two-way (AV/OV), determining which thematic
    role occupies the extractable pivot position. -/
theorem voice_determines_pivot :
    Fragments.TobaBatak.Voice.av.pivotRole = .agent ∧
    Fragments.TobaBatak.Voice.ov.pivotRole = .patient := ⟨rfl, rfl⟩

-- ============================================================================
-- § 10: Decidable C-Command
-- ============================================================================

/-- `decide` confirmation of `vp_ccommands_subject`'s structured proof. -/
theorem vp_ccommands_subject_decide :
    cCommandsIn tobaBatakVOS.final vp n_dakdanakan := by
  native_decide

-- ============================================================================
-- § 11: Toba Batak SVO via the VOS Hypothesis (§5 of the paper)
-- ============================================================================

/-! ### The VOS Hypothesis

@cite{cole-hermon-2008} §5: SVO order is common in Toba Batak (~1/3 of
sentences). Two competing analyses:

- **SVO Hypothesis**: SVO sentences have underlying SVO and VoiceP never
  raises. Predicts different extraction restrictions for SVO vs VOS.
- **VOS Hypothesis**: ALL clauses go through a VOS stage; SVO results
  from the subject raising past the fronted VoiceP to a higher specifier.
  Predicts the SAME extraction restrictions for SVO and VOS.

The data confirm the VOS Hypothesis: extraction from SVO clauses shows
the same freezing effects as VOS (examples 85–88). Direct objects cannot
be wh-fronted regardless of surface word order.

The derivation extends `tobaBatakVOS` with one more step: subject raises
to Spec,FP (a higher functional projection), past the fronted VP.

This analysis connects to the claim in §6 that linear order within Merge
is irrelevant — only c-command matters. This is precisely the content of
the Linear Correspondence Axiom (LCA) formalized in
`Theories.Interfaces.SyntaxPhonology.Minimalist.LCA`.
-/

/-- F head (higher functional projection above TP). -/
def f_head := mkLeaf .C [.T] 6

/-- Toba Batak SVO via the VOS Hypothesis.

    Steps 1–5 are identical to `tobaBatakVOS` (yielding VOS at stage 5).
    Then:
    6. EM-L F → `[FP F [TP VP [T' T [vP Subj [v' v tVP]]]]]`
    7. IM Subj → `[FP Subj [F' F [TP VP [T' T [vP tSubj [v' v tVP]]]]]]`

    The subject raises past the fronted VP, yielding S-V-O surface order. -/
def tobaBatakSVO : Derivation :=
  { initial := v_mangatuk
    steps := [
      .emR n_biangi,
      .emL v_head,
      .emL n_dakdanakan,
      .emL t_head,
      .im vp 0,
      .emL f_head,
      .im n_dakdanakan 1
    ] }

/-- The VOS Hypothesis derives SVO surface order. -/
theorem toba_batak_svo_order :
    tobaBatakSVO.final.phonYield = ["dakdanakan", "mangatuk", "biangi"] := by
  native_decide

/-- SVO goes through VOS: at stage 5 (before subject-raising), the
    intermediate tree has VOS order — the same as `tobaBatakVOS.final`. -/
theorem svo_passes_through_vos :
    (tobaBatakSVO.stageAt 5).phonYield = tobaBatakVOS.final.phonYield := by
  native_decide

/-- The VOS Hypothesis predicts identical extraction restrictions for SVO:
    the DO is still inside the fronted VP, regardless of whether the
    subject subsequently raises past it. -/
theorem svo_same_extraction_as_vos :
    containsB vp n_biangi = true ∧
    containsB vp n_dakdanakan = false := ⟨rfl, rfl⟩

/-- SVO requires two movement steps (VP-raising + subject-raising). -/
theorem svo_has_two_movements :
    tobaBatakSVO.movedItems.length = 2 := by native_decide

-- ============================================================================
-- § 12: English Passive Derivation (§7 of the paper)
-- ============================================================================

/-! ### English passives and the agent-as-adjunct analysis

@cite{cole-hermon-2008} §7 extends the VP-raising analysis to English
passives, predicting why English and Toba Batak differ on passive binding.

The key structural difference: in TB, the passive agent is an *argument*
generated in Spec,vP (high position, c-commands patient in VP). In
English, the passive agent is an *adjunct* (by-phrase, low position
inside VP, does not c-command patient).

Consequence:
- **TB passive**: agent c-commands patient at the base stage →
  reconstruction allows agent to bind reflexive patient (Type A).
  Patient raised to surface subject also c-commands agent (Type B).
- **English passive**: agent never c-commands patient → agent cannot
  bind reflexive patient (example 96: "*himself was injured by the boy").
  Patient raised to subject c-commands agent → patient can bind reflexive
  agent (example 95: "the boy was injured by himself").

We model the English passive with the agent as a low complement of V
(representing the by-phrase adjunct) and the patient as specifier of VP
(following @cite{larson-1988}), with no external argument in Spec,vP.
-/

def v_injured     := mkLeafPhon .V [] "was-injured" 21
def n_boy         := mkLeafPhon .N [] "the-boy" 22
def n_by_himself  := mkLeafPhon .N [] "by-himself" 23
def v_head_pass   := mkLeaf .v [.V] 24
def t_head_pass   := mkLeaf .T [.v] 25

/-- The passive VP: `[VP patient [V' V agent-PP]]`. -/
def vp_passive : SyntacticObject := .node n_boy (.node v_injured n_by_himself)

/-- English passive derivation (trees 97–100 of the paper).

    Steps:
    1. EM-R agent-PP → `[V' V agent]`
    2. EM-L patient  → `[VP patient [V' V agent]]`
    3. EM-L v        → `[v' v VP]` (no external argument — passive)
    4. EM-L T        → `[TP T [vP v VP]]`
    5. IM patient    → `[TP patient [T' T [vP v [VP t [V' V agent]]]]]` -/
def englishPassive : Derivation :=
  { initial := v_injured
    steps := [
      .emR n_by_himself,
      .emL n_boy,
      .emL v_head_pass,
      .emL t_head_pass,
      .im n_boy 0
    ] }

/-- English passive yields patient-verb-agent surface order. -/
theorem english_passive_order :
    englishPassive.final.phonYield = ["the-boy", "was-injured", "by-himself"] := by
  native_decide

-- ============================================================================
-- § 13: Cross-Linguistic Binding Contrast (§7 of the paper)
-- ============================================================================

/-! ### TB vs English passive binding

The same theory (c-command based binding + optional reconstruction)
with different structural parameters (agent-as-argument vs
agent-as-adjunct) correctly predicts the cross-linguistic contrast:

| Pattern                        | Toba Batak | English |
|--------------------------------|------------|---------|
| Agent antecedes patient refl.  | ✓ (Type A) | ✗ (96) |
| Patient antecedes agent refl.  | ✓ (Type B) | ✓ (95) |

Both predictions follow from c-command in the derived tree:
- TB agent (Spec,vP) c-commands patient (VP) at base → reconstruction
- English agent (low PP) does not c-command patient at any stage
- Both: patient (raised to Spec,TP/FP) c-commands agent

The formalization verifies the c-command predictions computationally
using `cCommandsIn` over the derived trees.
-/

/-- In the English passive, the patient (raised to Spec,TP) c-commands
    the by-phrase agent. This is why "The boy was injured by himself" is
    grammatical: the patient can bind a reflexive in the agent position. -/
theorem english_passive_patient_ccommands_agent :
    cCommandsIn englishPassive.final n_boy n_by_himself := by
  native_decide

/-- In the English passive, the by-phrase agent does NOT c-command the
    patient. This is why "*Himself was injured by the boy" is
    ungrammatical: the agent (low adjunct inside VP) cannot bind a
    reflexive in subject position. -/
theorem english_passive_agent_not_ccommands_patient :
    ¬ cCommandsIn englishPassive.final n_by_himself n_boy := by
  native_decide

/-- In the TB active **base structure** (pre-movement, stage 4), the
    subject c-commands the object. This is the structural basis for
    Type A binding (active subject → DO refl).

    Binding is evaluated at the pre-movement stage: the base tree is
    `[TP T [vP Subj [v' v [VP V Obj]]]]`, where Subj's sister (v')
    contains the object. After VP-raising, the object moves to a
    different branch; reconstruction restores the base c-command. -/
theorem tb_active_subject_ccommands_object_at_base :
    cCommandsIn (tobaBatakVOS.stageAt 4) n_dakdanakan n_biangi := by
  native_decide

/-- Cross-linguistic contrast verified: same c-command theory, different
    structural parameters, different binding predictions.

    The conjunction links four c-command checks across two languages:
    1. TB active (base): subject c-commands object (Type A binding)
    2. TB active (derived): object does not c-command subject (Type C)
    3. English passive (derived): patient c-commands agent (ex. 95)
    4. English passive (derived): agent does not c-command patient (ex. 96) -/
theorem cross_linguistic_binding_contrast :
    -- TB active (base stage for binding, derived stage for anti-binding)
    cCommandsIn (tobaBatakVOS.stageAt 4) n_dakdanakan n_biangi ∧
    ¬ cCommandsIn tobaBatakVOS.final n_biangi n_dakdanakan ∧
    -- English passive (derived tree)
    cCommandsIn englishPassive.final n_boy n_by_himself ∧
    ¬ cCommandsIn englishPassive.final n_by_himself n_boy := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end ColeHermon2008

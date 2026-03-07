import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Derivation
import Linglib.Theories.Syntax.Minimalism.Core.EPP
import Linglib.Theories.Syntax.Minimalism.Core.Position
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

namespace Phenomena.WordOrder.Studies.ColeHermon2008

open Minimalism

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
         ⟨_, self_mem_subterms _, Or.inl rfl, Or.inr rfl, by decide⟩,
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
`Fragments.TobaBatak.Basic` and verified in `Phenomena.FillerGap.TobaBatak`.
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
  deriving Repr, DecidableEq, BEq

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
    cCommandsInB tobaBatakVOS.final n_biangi n_dakdanakan = false := by
  native_decide

-- ============================================================================
-- § 9: Integration Bridges
-- ============================================================================

/-! ### Connecting to Toba Batak extraction infrastructure

The VP-raising analysis's extraction predictions are independently
formalized in `Fragments.TobaBatak.Basic` (empirical extraction data)
and `Phenomena.FillerGap.TobaBatak` (verification theorems). This
section bridges the derivational analysis to that data.
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

end Phenomena.WordOrder.Studies.ColeHermon2008

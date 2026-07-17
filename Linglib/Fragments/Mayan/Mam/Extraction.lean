import Linglib.Morphology.Focus
import Linglib.Syntax.Extraction
import Linglib.Data.UD.Basic

/-!
# Mam Extraction Morphology Fragment

Theory-neutral data on extraction morphology in San Juan Ostuncalco
(SJO) Mam (Mayan, Western Highlands of Guatemala), following
[elkins-torrence-brown-2026]. When an oblique undergoes Ā-movement
(wh-movement, focus fronting, relativization), the optional enclitic
=(y)a' may appear on the verbal complex — on Voice⁰ or Dir⁰
(directional auxiliary). Its distribution is conditioned by clause size
(licensed only where Voice⁰ projects; impossible in VP-sized infinitival
complements, [elkins-torrence-brown-2026] §6) and by extraction target
(oblique extraction only — subject extraction triggers Agent Focus *-a*,
object extraction triggers neither, §3.1; temporal 'when' obliques also
do not trigger it, §8.1).

The central finding is multiple spellout: in long-distance extraction
through full CPs and aspectless clauses, =(y)a' can appear on both the
matrix and embedded predicates — one per Voice/Dir head along the
successive-cyclic movement path (Table 4, §6.2).

## Main declarations

* `Mam.MamClauseType` with `.projectsVoice`: the three clause sizes
  (full CP, aspectless, infinitival) and whether each projects Voice.
* `Mam.MamExtractionDatum`, `Mam.monoData`: monoclausal extraction data
  points and their pooled list.
* `Mam.MamLongDistanceDatum`, `Mam.ldData`: long-distance data tracking
  =(y)a' on the matrix and embedded predicates independently (Table 4).
* `Mam.eqya_iff_voice_and_oblique`: the core generalization — =(y)a' is
  licensed iff the clause projects Voice and a non-temporal oblique
  extracts.
* `Mam.MovementReflex` with `.islandSensitive`: island sensitivity
  derived from movement being phase-bounded rather than stipulated.
* `Mam.Extraction.realize`: the AF- and =(y)a'-based extraction marking,
  with `Mam.Extraction.strategy` as the WALS-style label.

## Implementation notes

All data is from [elkins-torrence-brown-2026], "Wh-movement paths and
oblique extraction in Mam (Mayan)", cited by section/example number.
-/

open Extraction (ExtractionTarget ExtractionMarkingStrategy Marked)

namespace Mam

/-! ### Clause types -/

/-- The three clause sizes relevant for =(y)a' distribution — different
    structural sizes of the verbal domain ([elkins-torrence-brown-2026]
    §6.1, following [coon-2019]). -/
inductive MamClauseType where
  /-- Full finite clause with aspect; projects Voice, so =(y)a' is
      licensed on oblique extraction. -/
  | fullCP
  /-- VoiceP-sized complement: no aspect but projects Voice, so =(y)a'
      is licensed ([elkins-torrence-brown-2026] §6.1). -/
  | aspectless
  /-- VP-sized infinitival complement: no Voice projected, so =(y)a' is
      impossible — no Voice⁰ to host [oblique] ([elkins-torrence-brown-2026] §6.1). -/
  | infinitival
  deriving DecidableEq, Repr

/-- Does this clause type project Voice? -/
def MamClauseType.projectsVoice : MamClauseType → Bool
  | .fullCP => true
  | .aspectless => true
  | .infinitival => false

/-! ### Extraction judgments -/

/-- Status of =(y)a' in a configuration — `licensed` (may grammatically
    appear; it is an optional enclitic) or `blocked`; optionality when
    licensed is orthogonal to the distributional constraints. -/
inductive MamExtractionJudgment where
  /-- =(y)a' is licensed (may appear) in this configuration -/
  | licensed
  /-- =(y)a' is blocked (may not appear) in this configuration -/
  | blocked
  deriving DecidableEq, Repr

/-! ### Monoclausal data -/

/-- A monoclausal extraction data point: a clause type, what is extracted,
    and whether =(y)a' is licensed. -/
structure MamExtractionDatum where
  /-- Descriptive label -/
  label : String
  /-- Section/example reference in [elkins-torrence-brown-2026] -/
  reference : String
  /-- Type of clause -/
  clauseType : MamClauseType
  /-- Is an oblique being extracted? -/
  obliqueExtracted : Bool
  /-- Is the extracted oblique temporal ('when')? Temporal obliques do not
      trigger =(y)a' though genuinely oblique and extracted (§8.1, ex. 56)
      — encoded honestly rather than as `obliqueExtracted := false`. The
      paper leaves this unexplained: "we leave an account of this for
      future work" (§8.1). -/
  isTemporal : Bool := false
  /-- Judgment on =(y)a' -/
  judgment : MamExtractionJudgment
  deriving Repr

/-- Transitive clause, oblique extraction: =(y)a' licensed.
    "With what did María clean the window?" — =(y)a' on predicate.
    Elkins et al. §4.1, ex. (22b). -/
def transOblExtraction : MamExtractionDatum :=
  { label := "Transitive, oblique wh-extraction"
  , reference := "§4.1, ex. (22b)"
  , clauseType := .fullCP
  , obliqueExtracted := true
  , judgment := .licensed }

/-- Transitive clause, subject extraction: =(y)a' blocked.
    "Who opened the door?" — antipassive required, no =(y)a'.
    Elkins et al. §3.2, ex. (19). -/
def transSubjExtraction : MamExtractionDatum :=
  { label := "Transitive, subject wh-extraction (AF)"
  , reference := "§3.2, ex. (19)"
  , clauseType := .fullCP
  , obliqueExtracted := false
  , judgment := .blocked }

/-- Transitive clause, object extraction: =(y)a' blocked.
    "What did María open?" — no =(y)a'.
    Elkins et al. §3.2, ex. (18b). -/
def transObjExtraction : MamExtractionDatum :=
  { label := "Transitive, object wh-extraction"
  , reference := "§3.2, ex. (18b)"
  , clauseType := .fullCP
  , obliqueExtracted := false
  , judgment := .blocked }

/-- Passive clause, oblique extraction: =(y)a' licensed.
    "Where were the tortillas sold by Juan?" — =(y)a' co-occurs with passive *-njtz*.
    Elkins et al. §7.2, ex. (54). -/
def passiveOblExtraction : MamExtractionDatum :=
  { label := "Passive, oblique wh-extraction"
  , reference := "§7.2, ex. (54)"
  , clauseType := .fullCP
  , obliqueExtracted := true
  , judgment := .licensed }

/-- Temporal oblique extraction: =(y)a' BLOCKED. "When" (*b'iix taq*) does
    not trigger =(y)a', unlike spatial and other obliques (§8.1, ex. (56));
    encoded honestly as `obliqueExtracted := true, isTemporal := true`.
    Unexplained: "we leave an account of this for future work" (§8.1). -/
def temporalOblExtraction : MamExtractionDatum :=
  { label := "Temporal oblique wh-extraction (no MVMT)"
  , reference := "§8.1, ex. (56)"
  , clauseType := .fullCP
  , obliqueExtracted := true
  , isTemporal := true
  , judgment := .blocked }

/-- All monoclausal extraction data points. -/
def monoData : List MamExtractionDatum :=
  [ transOblExtraction
  , transSubjExtraction
  , transObjExtraction
  , passiveOblExtraction
  , temporalOblExtraction ]

/-! ### Long-distance data (Table 4) -/

/-- A long-distance extraction data point: tracks =(y)a' status on both
    the matrix and embedded predicates independently. This captures the
    paper's central empirical finding (Table 4, §6.2): =(y)a' can appear
    on BOTH predicates along the successive-cyclic movement path. -/
structure MamLongDistanceDatum where
  /-- Descriptive label -/
  label : String
  /-- Section/example reference -/
  reference : String
  /-- Type of embedded clause -/
  embeddedClauseType : MamClauseType
  /-- =(y)a' status on the matrix predicate -/
  matrixJudgment : MamExtractionJudgment
  /-- =(y)a' status on the embedded predicate -/
  embeddedJudgment : MamExtractionJudgment
  deriving Repr

/-- Long-distance extraction from full CP: =(y)a' licensed on BOTH
    matrix and embedded predicates. Table 4, Row 1; §6.2, ex. (38)–(39). -/
def ldFullCP : MamLongDistanceDatum :=
  { label := "LD extraction from full CP"
  , reference := "§6.2, Table 4, Row 1"
  , embeddedClauseType := .fullCP
  , matrixJudgment := .licensed
  , embeddedJudgment := .licensed }

/-- Long-distance extraction from aspectless clause: =(y)a' licensed on
    BOTH. Table 4, Row 2; §6.2. -/
def ldAspectless : MamLongDistanceDatum :=
  { label := "LD extraction from aspectless clause"
  , reference := "§6.2, Table 4, Row 2"
  , embeddedClauseType := .aspectless
  , matrixJudgment := .licensed
  , embeddedJudgment := .licensed }

/-- Long-distance extraction from infinitival: =(y)a' licensed on
    matrix but BLOCKED on embedded. Table 4, Row 3; §6.2, ex. (46). -/
def ldInfinitival : MamLongDistanceDatum :=
  { label := "LD extraction from infinitival"
  , reference := "§6.2, Table 4, Row 3"
  , embeddedClauseType := .infinitival
  , matrixJudgment := .licensed
  , embeddedJudgment := .blocked }

/-- Embedded question (1-step extraction): =(y)a' BLOCKED on matrix,
    licensed on embedded. Table 4, Row 4; §6.2, ex. (41). -/
def ldEmbeddedQuestion : MamLongDistanceDatum :=
  { label := "Embedded question (oblique EQ)"
  , reference := "§6.2, Table 4, Row 4"
  , embeddedClauseType := .fullCP
  , matrixJudgment := .blocked
  , embeddedJudgment := .licensed }

/-- All long-distance extraction data points (Table 4). -/
def ldData : List MamLongDistanceDatum :=
  [ ldFullCP, ldAspectless, ldInfinitival, ldEmbeddedQuestion ]

/-! ### Per-datum verification -/

theorem trans_obl_licensed : transOblExtraction.judgment = .licensed := rfl
theorem trans_subj_blocked : transSubjExtraction.judgment = .blocked := rfl
theorem trans_obj_blocked : transObjExtraction.judgment = .blocked := rfl
theorem passive_obl_licensed : passiveOblExtraction.judgment = .licensed := rfl
theorem temporal_obl_blocked : temporalOblExtraction.judgment = .blocked := rfl

/-! ### Generalizations -/

/-- Core generalization (monoclausal): =(y)a' is licensed iff the clause
    projects Voice AND a non-temporal oblique is extracted.

    The `!d.isTemporal` conjunct is a stipulation — the paper does not
    explain why temporal obliques are exempt (§8.1). It is separated out
    as a distinct condition rather than hidden in `obliqueExtracted`. -/
theorem eqya_iff_voice_and_oblique :
    monoData.all (λ d =>
      (d.clauseType.projectsVoice && d.obliqueExtracted && !d.isTemporal) ==
      (d.judgment == .licensed)) = true := by
  decide

/-- Multiple spellout: in long-distance extraction, =(y)a' is licensed
    on each predicate whose clause projects Voice. Matrix clause always
    projects Voice (it's a full CP). -/
theorem ld_embedded_tracks_voice :
    ldData.all (λ d =>
      d.embeddedClauseType.projectsVoice == (d.embeddedJudgment == .licensed)) = true := by
  decide

/-- =(y)a' tracks oblique, not extraction in general: subject and object
    extraction in the same clause size do not trigger =(y)a'. -/
theorem eqya_tracks_oblique_not_extraction :
    transSubjExtraction.clauseType = transOblExtraction.clauseType ∧
    transObjExtraction.clauseType = transOblExtraction.clauseType ∧
    transSubjExtraction.judgment = .blocked ∧
    transObjExtraction.judgment = .blocked ∧
    transOblExtraction.judgment = .licensed := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Temporal obliques are genuine obliques that undergo genuine extraction,
    but are exempt from =(y)a' marking. This is an open question. -/
theorem temporal_is_oblique_but_exempt :
    temporalOblExtraction.obliqueExtracted = true ∧
    temporalOblExtraction.isTemporal = true ∧
    temporalOblExtraction.judgment = .blocked := ⟨rfl, rfl, rfl⟩

/-! ### Island sensitivity -/

/-- A morphological reflex of Ā-movement inherits movement's locality:
    since Ā-movement is phase-bounded (Phase Impenetrability Condition,
    `Phase.lean`), any morpheme requiring movement through a probe's
    specifier is island-sensitive. Deriving island sensitivity from these
    two properties replaces a stipulated `Bool` ([chomsky-2000] on PIC;
    [elkins-torrence-brown-2026] §7.1). -/
structure MovementReflex where
  /-- Spellout of features valued via Agree with an Ā-moved constituent
      (Agree analysis, §5). -/
  requiresMovement : Bool
  /-- Movement is phase-bounded (PIC, `Phase.lean`); islands are
      configurations where the phase edge is unavailable. -/
  movementPhaseBounded : Bool
  deriving DecidableEq, Repr

/-- Island sensitivity is derived: a movement reflex is island-sensitive
    iff the morpheme requires movement AND movement is phase-bounded.
    No movement → no Agree → no spellout. -/
def MovementReflex.islandSensitive (mr : MovementReflex) : Bool :=
  mr.requiresMovement && mr.movementPhaseBounded

/-- =(y)a' is a movement reflex: it requires Ā-movement of the oblique
    through Spec,VoiceP (so Voice can Agree [uOblique]), and movement
    is phase-bounded (PIC). -/
def eqyaMovementReflex : MovementReflex :=
  { requiresMovement := true
  , movementPhaseBounded := true }

/-- Island sensitivity of =(y)a' follows from its being a movement reflex.
    Derived from `requiresMovement ∧ movementPhaseBounded`, not stipulated. -/
def eqyaIslandSensitive : Bool := eqyaMovementReflex.islandSensitive

/-- Proof that the derivation yields island sensitivity. -/
theorem eqya_island_sensitive_derived :
    eqyaMovementReflex.islandSensitive = true := rfl

/-! ### Against Agent Focus -/

/-- =(y)a' co-occurs with passive morphology *-njtz* ([elkins-torrence-brown-2026]
    §7.2, ex. (53)–(54)): passive is conditioned by `Voice.Flavor` and
    =(y)a' by [+oblique] features — independent fields in `Voice.Head`, so
    the flavor does not affect the features (structural derivation in
    `MinimalismOblExtraction.eqya_not_agent_focus`). -/
theorem passive_oblique_cooccurrence :
    passiveOblExtraction.judgment = .licensed := rfl

/-! ### Extraction marking -/

namespace Extraction

/-- Reflex hosts for SJA Mam extraction marking: the verb (AF suffixes)
    and the Voice/Dir head hosting =(y)a'. -/
inductive Site where
  | verb
  | voiceHead
  deriving DecidableEq, Repr

/-- SJA Mam marks two extraction cells. Subject (A) extraction switches
    the verb to AF ([scott-2023] §2.5.4.1 ex. 169, §2.7.1), combining
    the antipassive suffix *-(a)n* with the AF-specific *-ta*
    (`b'yo-n-ta` 'hit-AP-AF') — morphologically distinct from K'iche''s
    bare antipassive *-n* ([mondloch-2017] Lesson 22); the SSAL-repair
    analysis lives in `Studies/Erlewine2016.lean`, and rival accounts
    are not encoded here. Oblique extraction places =(y)a' on the
    Voice/Dir head — conditioned by clause size, exempting temporal
    obliques (§8.1), island-sensitive (§7.1). Core-object extraction is
    unmarked. -/
def realize : ExtractionTarget → List (Morphology.Focus.Reflex Site)
  | .subject => [.morpheme .verb]
  | .oblique => [.morpheme .voiceHead]
  | _ => []

/-- WALS-style label: dedicated morphemes mark extraction. -/
def strategy : ExtractionMarkingStrategy := .dedicatedMorpheme

theorem marks_oblique : Marked realize .oblique := by decide

/-- =(y)a' tracks obliques, not subjects: no voice-head reflex under
    subject extraction (subject marking is verb-hosted AF instead). -/
theorem eqya_not_on_subject :
    Morphology.Focus.Reflex.morpheme Site.voiceHead ∉ realize .subject := by decide

end Extraction

end Mam

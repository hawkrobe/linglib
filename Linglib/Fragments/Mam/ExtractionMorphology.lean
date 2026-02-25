import Linglib.Core.Interfaces.ExtractionMorphology
import Linglib.Core.Lexical.Word

/-!
# Mam Extraction Morphology Fragment @cite{elkins-imanishi-coon-2026}

Theory-neutral data on extraction morphology in San Juan Ostuncalco (SJO) Mam,
a Mayan language spoken in the Western Highlands of Guatemala.

## The Phenomenon

When an oblique argument undergoes Ā-movement (wh-movement, focus fronting,
relativization) in Mam, the **optional** enclitic =(y)a' may appear on the
verbal complex — specifically on Voice⁰ or Dir⁰ (directional auxiliary).
Its distribution is conditioned by two factors:

1. **Clause size**: =(y)a' is licensed only in clauses that project Voice⁰.
   In infinitival complements (VP-sized, lacking Voice), =(y)a' is impossible
   even when an oblique has extracted (Elkins et al. §6).

2. **Extraction target**: =(y)a' marks specifically *oblique* extraction.
   Subject extraction triggers Agent Focus (*-a*), not =(y)a'. Object
   extraction triggers neither (§3.1). Temporal obliques ('when') also do
   not trigger =(y)a' (§8.1).

## Key Empirical Finding: Multiple Spellout

In long-distance extraction through full CPs and aspectless clauses, =(y)a'
can appear on BOTH the matrix and embedded predicates — one per Voice/Dir
head along the successive-cyclic movement path (Table 4, §6.2).

## Data Sources

All data from Elkins, Imanishi & Coon (2026), "Wh-movement and oblique
extraction in SJO Mam". Examples cited by section/example number.

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
-/

namespace Fragments.Mam

-- ============================================================================
-- § 1: Clause Types
-- ============================================================================

/-- The three clause sizes relevant for =(y)a' distribution in Mam.
    These correspond to different structural sizes of the verbal domain
    (Elkins et al. 2026 §6.1, following Coon 2019 and Elkins et al. 2025):

    - `fullCP`: Full finite clause with aspect — projects Voice
    - `aspectless`: VoiceP-sized complement (no aspect) — projects Voice
    - `infinitival`: VP-sized complement (Elkins et al. 2026, §6.1) — does NOT project Voice -/
inductive MamClauseType where
  /-- Full finite clause with aspect marking. Projects the full verbal
      spine including Voice. =(y)a' licensed on oblique extraction. -/
  | fullCP
  /-- VoiceP-sized complement: lacks aspect but projects Voice.
      =(y)a' licensed on oblique extraction (Elkins et al. §6.1,
      following Elkins et al. 2025). -/
  | aspectless
  /-- VP-sized infinitival complement (Elkins et al. 2026, §6.1): no Voice projected.
      =(y)a' impossible — no Voice⁰ to host [oblique] (Elkins et al. §6.1). -/
  | infinitival
  deriving DecidableEq, BEq, Repr

/-- Does this clause type project Voice? -/
def MamClauseType.projectsVoice : MamClauseType → Bool
  | .fullCP => true
  | .aspectless => true
  | .infinitival => false

-- ============================================================================
-- § 2: Extraction Judgments
-- ============================================================================

/-- Judgment on the status of =(y)a' in a given configuration.
    Note: =(y)a' is an **optional** enclitic (Elkins et al. 2026, p.11, §8.2).
    `licensed` means =(y)a' may grammatically appear; `blocked` means it may
    not. The optionality of =(y)a' when licensed is orthogonal to its
    distributional constraints. -/
inductive MamExtractionJudgment where
  /-- =(y)a' is licensed (may appear) in this configuration -/
  | licensed
  /-- =(y)a' is blocked (may not appear) in this configuration -/
  | blocked
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 3: Monoclausal Data
-- ============================================================================

/-- A monoclausal extraction data point: a clause type, what is extracted,
    and whether =(y)a' is licensed. -/
structure MamExtractionDatum where
  /-- Descriptive label -/
  label : String
  /-- Section/example reference in Elkins et al. (2026) -/
  reference : String
  /-- Type of clause -/
  clauseType : MamClauseType
  /-- Is an oblique being extracted? -/
  obliqueExtracted : Bool
  /-- Judgment on =(y)a' -/
  judgment : MamExtractionJudgment
  deriving Repr

/-- Transitive clause, oblique extraction: =(y)a' licensed.
    "Where did the man buy the tortillas?" — =(y)a' on Dir⁰.
    Elkins et al. §3.1, ex. (8). -/
def transOblExtraction : MamExtractionDatum :=
  { label := "Transitive, oblique wh-extraction"
  , reference := "§3.1, ex. (8)"
  , clauseType := .fullCP
  , obliqueExtracted := true
  , judgment := .licensed }

/-- Transitive clause, subject extraction: =(y)a' blocked.
    "Who bought the tortillas?" — Agent Focus (*-a*) instead, no =(y)a'.
    Elkins et al. §3.1, ex. (6). -/
def transSubjExtraction : MamExtractionDatum :=
  { label := "Transitive, subject wh-extraction (AF)"
  , reference := "§3.1, ex. (6)"
  , clauseType := .fullCP
  , obliqueExtracted := false
  , judgment := .blocked }

/-- Transitive clause, object extraction: =(y)a' blocked.
    "What did the man buy?" — no =(y)a'.
    Elkins et al. §3.1, ex. (7). -/
def transObjExtraction : MamExtractionDatum :=
  { label := "Transitive, object wh-extraction"
  , reference := "§3.1, ex. (7)"
  , clauseType := .fullCP
  , obliqueExtracted := false
  , judgment := .blocked }

/-- Passive clause, oblique extraction: =(y)a' licensed.
    "Where were the tortillas bought?" — =(y)a' appears even without agent.
    Elkins et al. §4.1, ex. (17)–(18). -/
def passiveOblExtraction : MamExtractionDatum :=
  { label := "Passive, oblique wh-extraction"
  , reference := "§4.1, ex. (17)–(18)"
  , clauseType := .fullCP
  , obliqueExtracted := true
  , judgment := .licensed }

/-- Temporal oblique extraction: =(y)a' BLOCKED.
    "When" (*b'iix taq*) does not trigger =(y)a', unlike spatial and
    other obliques. Elkins et al. §8.1, ex. (56). -/
def temporalOblExtraction : MamExtractionDatum :=
  { label := "Temporal oblique wh-extraction (no MVMT)"
  , reference := "§8.1, ex. (56)"
  , clauseType := .fullCP
  , obliqueExtracted := false  -- false: temporal obliques don't count as [oblique]
  , judgment := .blocked }

/-- All monoclausal extraction data points. -/
def monoData : List MamExtractionDatum :=
  [ transOblExtraction
  , transSubjExtraction
  , transObjExtraction
  , passiveOblExtraction
  , temporalOblExtraction ]

-- ============================================================================
-- § 4: Long-Distance (Biclausal) Data — Table 4
-- ============================================================================

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
    matrix and embedded predicates. Table 4, Row 1; §6.2, ex. (39)–(40). -/
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
    matrix but BLOCKED on embedded. Table 4, Row 3; §6.2, ex. (45)–(46). -/
def ldInfinitival : MamLongDistanceDatum :=
  { label := "LD extraction from infinitival"
  , reference := "§6.2, Table 4, Row 3"
  , embeddedClauseType := .infinitival
  , matrixJudgment := .licensed
  , embeddedJudgment := .blocked }

/-- Embedded question (1-step extraction): =(y)a' BLOCKED on matrix,
    licensed on embedded. Table 4, Row 4; §4.2, ex. (25)–(26). -/
def ldEmbeddedQuestion : MamLongDistanceDatum :=
  { label := "Embedded question (oblique EQ)"
  , reference := "§4.2, Table 4, Row 4"
  , embeddedClauseType := .fullCP
  , matrixJudgment := .blocked
  , embeddedJudgment := .licensed }

/-- All long-distance extraction data points (Table 4). -/
def ldData : List MamLongDistanceDatum :=
  [ ldFullCP, ldAspectless, ldInfinitival, ldEmbeddedQuestion ]

-- ============================================================================
-- § 5: Per-Datum Verification (Monoclausal)
-- ============================================================================

theorem trans_obl_licensed : transOblExtraction.judgment = .licensed := rfl
theorem trans_subj_blocked : transSubjExtraction.judgment = .blocked := rfl
theorem trans_obj_blocked : transObjExtraction.judgment = .blocked := rfl
theorem passive_obl_licensed : passiveOblExtraction.judgment = .licensed := rfl
theorem temporal_obl_blocked : temporalOblExtraction.judgment = .blocked := rfl

-- ============================================================================
-- § 6: Generalizations
-- ============================================================================

/-- Core generalization (monoclausal): =(y)a' is licensed iff the clause
    projects Voice AND a (non-temporal) oblique is extracted. -/
theorem eqya_iff_voice_and_oblique :
    monoData.all (λ d =>
      (d.clauseType.projectsVoice && d.obliqueExtracted) ==
      (d.judgment == .licensed)) = true := by
  native_decide

/-- Multiple spellout: in long-distance extraction, =(y)a' is licensed
    on each predicate whose clause projects Voice. Matrix clause always
    projects Voice (it's a full CP). -/
theorem ld_embedded_tracks_voice :
    ldData.all (λ d =>
      d.embeddedClauseType.projectsVoice == (d.embeddedJudgment == .licensed)) = true := by
  native_decide

/-- =(y)a' tracks oblique, not extraction in general: subject and object
    extraction in the same clause size do not trigger =(y)a'. -/
theorem eqya_tracks_oblique_not_extraction :
    transSubjExtraction.clauseType = transOblExtraction.clauseType ∧
    transObjExtraction.clauseType = transOblExtraction.clauseType ∧
    transSubjExtraction.judgment = .blocked ∧
    transObjExtraction.judgment = .blocked ∧
    transOblExtraction.judgment = .licensed := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Island Sensitivity (§7.1)
-- ============================================================================

/-- =(y)a' is island-sensitive: it cannot appear when the oblique is
    extracted from within a syntactic island. This argues against a
    resumptive-pronoun analysis, since resumptives typically rescue
    island violations. Elkins et al. §7.1, ex. (50)–(52). -/
def eqyaIslandSensitive : Bool := true

-- ============================================================================
-- § 8: Against Agent Focus (§7.2)
-- ============================================================================

/-- =(y)a' co-occurs with passive voice morphology (*-njtz*), while
    Agent Focus (*-a*) is in complementary distribution with voice
    morphemes. This shows =(y)a' is not an instance of AF.
    Elkins et al. §7.2, ex. (53)–(54). -/
def eqyaCooccursWithPassive : Bool := true

/-- Agent Focus (*-a*) is restricted to the embedded clause in
    long-distance subject extraction. =(y)a' appears on BOTH matrix
    and embedded predicates in LD oblique extraction. This further
    distinguishes the two morphemes. Elkins et al. §7.2. -/
def eqyaMultipleSpellout : Bool := true

-- ============================================================================
-- § 9: Extraction Profile
-- ============================================================================

/-- Mam extraction profile: dedicated morpheme strategy, marks oblique only.
    Excludes temporal obliques (§8.1). -/
def mamExtractionProfile : Interfaces.ExtractionProfile :=
  { language := "Mam (SJO)"
  , strategy := .dedicatedMorpheme
  , markedPositions := [.oblique]
  , distinguishesPosition := true
  , notes := "Optional enclitic =(y)a' on Voice⁰/Dir⁰ marks oblique extraction; " ++
             "absent for subject (AF) and object extraction; " ++
             "conditioned by clause size (requires Voice projection); " ++
             "temporal obliques exempt (§8.1); island-sensitive (§7.1)" }

theorem mam_marks_oblique :
    mamExtractionProfile.marks .oblique = true := by native_decide
theorem mam_no_mark_subject :
    mamExtractionProfile.marks .subject = false := by native_decide

end Fragments.Mam

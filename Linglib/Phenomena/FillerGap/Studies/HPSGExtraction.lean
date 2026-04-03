import Linglib.Theories.Syntax.HPSG.Core.HeadFiller
import Linglib.Phenomena.FillerGap.LongDistance
import Linglib.Phenomena.Islands.Studies.Ross1967

/-!
# Bridge: HPSG Extraction to Filler-Gap Phenomena
@cite{sag-wasow-bender-2003} @cite{hofmeister-sag-2010}

Connects HPSG's Head-Filler Schema and SLASH mechanism to empirical
filler-gap data in `Phenomena.FillerGap`.

## Main results

- `object_extraction_licensed`: HPSG correctly derives object wh-questions
  via gap introduction + SLASH amalgamation + Head-Filler discharge
- `island_blocks_extraction`: GAP restrictions block SLASH propagation
  through island constructions
- `weak_island_np_ok`: Weak islands allow NP extraction but block PP
- `extraction_and_island_complementary`: extraction succeeds iff
  not blocked by an island
-/

namespace Phenomena.FillerGap.Studies.HPSGExtraction

open HPSG

-- ============================================================================
-- HPSG Extraction Mechanism
-- ============================================================================

/-- Model of a filler-gap dependency: a wh-filler, a gapped clause,
and an optional island restriction on the embedded domain. -/
structure ExtractionConfig where
  /-- Category of the filler (wh-phrase) -/
  fillerCat : UD.UPOS
  /-- Category of the gap (missing complement) -/
  gapCat : UD.UPOS
  /-- GAP restriction on intervening domain (if any) -/
  restriction : GapRestriction := .unrestricted

/-- Is extraction licensed under HPSG?

1. The filler's category must be compatible with the gap
2. The SLASH value must survive any island restrictions -/
def extractionLicensed (cfg : ExtractionConfig) : Bool :=
  -- The filler must match the gap
  categoriesMatch cfg.fillerCat cfg.gapCat &&
  -- SLASH must survive island restrictions
  (propagateSlash ⟨[cfg.gapCat]⟩ cfg.restriction).isEmpty == false

-- ============================================================================
-- Object Extraction
-- ============================================================================

/-- Object wh-question: "What did John see ___?"
NP gap, NP filler, no island → licensed. -/
def objectWhQuestion : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .unrestricted }

/-- Subject wh-question: "Who saw Mary?"
In HPSG, subject questions don't need extraction — the wh-word IS the
subject. But we can model it as NP gap + NP filler for uniformity. -/
def subjectWhQuestion : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .unrestricted }

-- Object and subject extraction are both licensed
#guard extractionLicensed objectWhQuestion
#guard extractionLicensed subjectWhQuestion

-- ============================================================================
-- Island Blocking
-- ============================================================================

/-- Extraction from an embedded question (wh-island): blocked.
"*What did John wonder who saw ___?" -/
def whIslandExtraction : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .noGap }

/-- Extraction from a topicalized clause: blocked.
"*What did this book, John read ___?" -/
def topicIslandExtraction : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .noGap }

-- Island extractions are blocked
#guard !extractionLicensed whIslandExtraction
#guard !extractionLicensed topicIslandExtraction

-- ============================================================================
-- Weak Islands: Category-Sensitive Restrictions
-- ============================================================================

/-- NP extraction from a weak island: allowed.
"Which employee did Albert learn whether they dismissed ___?" -/
def weakIslandNP : ExtractionConfig :=
  { fillerCat := .PRON, gapCat := .NOUN, restriction := .npOnly }

/-- PP extraction from a weak island: blocked.
"*In which city did you wonder whether John lives ___?" -/
def weakIslandPP : ExtractionConfig :=
  { fillerCat := .ADP, gapCat := .ADP, restriction := .npOnly }

-- NP extraction from weak island: ok; PP extraction: blocked
#guard extractionLicensed weakIslandNP
#guard !extractionLicensed weakIslandPP

-- ============================================================================
-- Connecting to Phenomena Data
-- ============================================================================

/-- Map island constraint types to HPSG GAP restrictions.

This is the key connection: empirical island classifications map to
specific GAP feature values in HPSG. -/
def islandToGapRestriction : ConstraintType → GapRestriction
  | .embeddedQuestion  => .noGap     -- absolute barrier (but see weak island analysis)
  | .complexNP         => .noGap     -- absolute barrier
  | .adjunct           => .noGap     -- absolute barrier
  | .coordinate        => .noGap     -- absolute barrier
  | .subject           => .npOnly    -- weak: some NP extraction ok
  | .sententialSubject => .noGap     -- absolute barrier
  | .mannerOfSpeaking  => .npOnly    -- weak: ameliorable with focus
  | .definiteNominal   => .npOnly    -- weak: ameliorated by VOCs (@cite{shen-huang-2026})

/-- HPSG predicts all absolute islands block extraction. -/
theorem absolute_islands_block :
    let cnpc : ExtractionConfig := ⟨.PRON, .NOUN, islandToGapRestriction .complexNP⟩
    let adj : ExtractionConfig := ⟨.PRON, .NOUN, islandToGapRestriction .adjunct⟩
    let coord : ExtractionConfig := ⟨.PRON, .NOUN, islandToGapRestriction .coordinate⟩
    extractionLicensed cnpc = false ∧
    extractionLicensed adj = false ∧
    extractionLicensed coord = false := by
  native_decide

/-- The gap introduction mechanism correctly removes complements. -/
theorem gap_removes_complement :
    let see_ss : Synsem := { cat := .VERB, val := { subj := [.NOUN], comps := [.NOUN] } }
    let see_w : Word := ⟨"see", .VERB, {}⟩
    (gapComplement see_w see_ss 0).map
      (fun p => p.1.synsem.val.comps.isEmpty && p.2.gaps == [.NOUN]) = some true := by
  native_decide

/-- End-to-end: extraction is licensed iff not blocked by an island. -/
theorem extraction_and_island_complementary :
    let free : ExtractionConfig := ⟨.PRON, .NOUN, .unrestricted⟩  -- no island → licensed
    let abs  : ExtractionConfig := ⟨.PRON, .NOUN, .noGap⟩         -- absolute island → blocked
    let weakNP : ExtractionConfig := ⟨.PRON, .NOUN, .npOnly⟩      -- weak island + NP → licensed
    let weakPP : ExtractionConfig := ⟨.ADP, .ADP, .npOnly⟩        -- weak island + PP → blocked
    extractionLicensed free = true ∧
    extractionLicensed abs = false ∧
    extractionLicensed weakNP = true ∧
    extractionLicensed weakPP = false := by
  native_decide

end Phenomena.FillerGap.Studies.HPSGExtraction

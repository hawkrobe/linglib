import Linglib.Core.WALS.Features.F92A
import Linglib.Core.WALS.Features.F93A
import Linglib.Core.WALS.Features.F116A

/-!
# Cross-Linguistic Question Typology
@cite{bhatt-dayal-2020} @cite{dayal-2025} @cite{mccloskey-2006} @cite{zu-2018}

Theory-neutral cross-linguistic data on question formation and embedding,
following @cite{dayal-2025}. Covers:

1. **Clause-typing variation**: forced (English, Italian) vs delayed (Hindi-Urdu)
2. **Simplex polar questions**: subordination restricted by clause-typing strategy
3. **Declarative questions**: bias conditioned by clause-typing
4. **Shiftiness**: responsive predicates shift under negation/questioning
5. **Conjunct/disjunct marking**: Newari person-sensitive verb morphology

Q-particle data classified by left-peripheral layer (which imports from
Theories/) lives in `Questions.TypologyBridge`.

## Languages covered

- English, Hindi-Urdu, Japanese, Italian, Newari

-/

namespace Phenomena.Questions.Typology

-- ============================================================================
-- B. Clause-typing variation (@cite{dayal-2025}: §4.4)
-- ============================================================================

/-- How a language handles clause-typing for polar questions at CP. -/
inductive ClauseTypingStrategy where
  | forced       -- Clause-typing forced at CP (English, Italian: whether/se)
  | delayed      -- Clause-typing delayed to PerspP (Hindi-Urdu: no wh-complementizer)
  deriving DecidableEq, Repr

/-- Data on simplex polar question embedding across languages.
    A simplex polar question is just the nucleus *p* (no "or not").
    Hindi-Urdu: simplex polars in matrix/quasi-sub but NOT subordination.
    English/Italian: simplex polars in all three positions (via whether/se). -/
structure SimplexPolarDatum where
  language : String
  clauseTyping : ClauseTypingStrategy
  /-- Simplex polar in matrix? -/
  matrixOk : Bool
  /-- Simplex polar in quasi-subordination? -/
  quasiSubOk : Bool
  /-- Simplex polar in subordination? -/
  subordinationOk : Bool
  deriving Repr

def english_simplex : SimplexPolarDatum :=
  { language := "English", clauseTyping := .forced
  , matrixOk := true, quasiSubOk := true, subordinationOk := true }

def italian_simplex : SimplexPolarDatum :=
  { language := "Italian", clauseTyping := .forced
  , matrixOk := true, quasiSubOk := true, subordinationOk := true }

-- Hindi-Urdu: simplex polar questions require PerspP (rising intonation activates
-- +WH at PerspP level). No wh-complementizer → cannot clause-type at CP.
-- @cite{dayal-2025}: (70)–(71)
def hindi_urdu_simplex : SimplexPolarDatum :=
  { language := "Hindi-Urdu", clauseTyping := .delayed
  , matrixOk := true, quasiSubOk := true, subordinationOk := false }

def allSimplexPolarData : List SimplexPolarDatum :=
  [english_simplex, italian_simplex, hindi_urdu_simplex]

/-- Delayed clause-typing languages cannot subordinate simplex polars. -/
theorem delayed_blocks_simplex_subordination :
    ∀ d ∈ allSimplexPolarData,
      d.clauseTyping = .delayed → d.subordinationOk = false := by
  intro d hd _
  simp [allSimplexPolarData] at hd
  rcases hd with rfl | rfl | rfl <;>
    simp_all [english_simplex, italian_simplex, hindi_urdu_simplex]

-- ============================================================================
-- C. Declarative questions and bias (@cite{dayal-2025}: §4.3)
-- ============================================================================

/-- Whether declarative questions in a language are obligatorily biased.
    English: "You drink wine?" is obligatorily biased (speaker expects yes).
    Hindi-Urdu/Italian: "a:p shara:b pi:te hai?" / "Bevi il vino?" can be neutral.
    This follows from whether clause-typing is forced at CP. -/
structure DeclarativeQuestionDatum where
  language : String
  /-- Can a rising declarative be a neutral (unbiased) question? -/
  neutralOk : Bool
  /-- Is a rising declarative always biased? -/
  obligatorilyBiased : Bool
  clauseTyping : ClauseTypingStrategy
  deriving Repr

def english_decl_q : DeclarativeQuestionDatum :=
  { language := "English"
  , neutralOk := false, obligatorilyBiased := true
  , clauseTyping := .forced }

def hindi_urdu_decl_q : DeclarativeQuestionDatum :=
  { language := "Hindi-Urdu"
  , neutralOk := true, obligatorilyBiased := false
  , clauseTyping := .delayed }

def italian_decl_q : DeclarativeQuestionDatum :=
  { language := "Italian"
  , neutralOk := true, obligatorilyBiased := false
  , clauseTyping := .forced }

def allDeclQData : List DeclarativeQuestionDatum :=
  [english_decl_q, hindi_urdu_decl_q, italian_decl_q]

-- ============================================================================
-- D. Hindi-Urdu shiftiness (@cite{dayal-2025}: §3.2, (39)–(41))
-- ============================================================================

/-- Cross-linguistic shiftiness data. Parallels McCloskey's English data.
    Hindi-Urdu *kya:* shows the same pattern as English embedded inversion:
    blocked under bare responsive, licensed under negation/questioning. -/
structure CrossLingShiftinessDatum where
  language : String
  verb : String
  sentence : String
  negated : Bool
  questioned : Bool
  quasiSubOk : Bool
  deriving Repr

-- Hindi-Urdu: "want to know" (rogative) freely takes kya: (@cite{dayal-2025}: (39a))
def hindi_urdu_want_to_know : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: ca:h-na: (want to know)"
  , sentence := "anu ja:nna: ca:hti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := true }

-- Hindi-Urdu: "know" (responsive) rejects kya: (@cite{dayal-2025}: (39b))
def hindi_urdu_know_bare : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "*anu ja:nti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := false }

-- Hindi-Urdu: "nobody knows" + kya: → OK (negation, @cite{dayal-2025}: (41a))
def hindi_urdu_know_negated : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "koii nahii jaanta [ki kya: TiTo sTa:lin-se mile the↑]"
  , negated := true, questioned := false, quasiSubOk := true }

-- Hindi-Urdu: "does anyone know" + kya: → OK (questioning, @cite{dayal-2025}: (41b))
def hindi_urdu_know_questioned : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "kisii-ko bhi maalum hai [ki (kya:) TiTo sTa:lin-se mile the↑]"
  , negated := false, questioned := true, quasiSubOk := true }

def allCrossLingShiftinessData : List CrossLingShiftinessDatum :=
  [hindi_urdu_want_to_know, hindi_urdu_know_bare,
   hindi_urdu_know_negated, hindi_urdu_know_questioned]

/-- Hindi-Urdu shiftiness parallels English: bare responsive blocks quasi-sub,
    negation and questioning license it. -/
theorem hindi_urdu_shiftiness_parallels_english :
    hindi_urdu_know_bare.quasiSubOk = false ∧
    hindi_urdu_know_negated.quasiSubOk = true ∧
    hindi_urdu_know_questioned.quasiSubOk = true := by
  simp [hindi_urdu_know_bare, hindi_urdu_know_negated, hindi_urdu_know_questioned]

-- ============================================================================
-- E. Newari conjunct/disjunct marking (@cite{dayal-2025}: §5.2, @cite{zu-2018})
-- ============================================================================

/-- Newari uses conjunct vs disjunct verb forms sensitive to whether the subject
    is coindexed with the perspectival center (Seat of Knowledge).
    - Declaratives: conjunct = 1st person subject (SoK = speaker)
    - Interrogatives: conjunct = 2nd person subject (SoK = addressee)
    This provides independent evidence for perspective shift in questions. -/
structure ConjunctDisjunctDatum where
  language : String
  clauseType : String  -- "declarative" or "interrogative"
  conjunctPerson : String  -- which person gets conjunct marking
  deriving Repr

def newari_declarative : ConjunctDisjunctDatum :=
  { language := "Newari", clauseType := "declarative"
  , conjunctPerson := "1st" }

def newari_interrogative : ConjunctDisjunctDatum :=
  { language := "Newari", clauseType := "interrogative"
  , conjunctPerson := "2nd" }

def allConjunctDisjunctData : List ConjunctDisjunctDatum :=
  [newari_declarative, newari_interrogative]

-- ============================================================================
-- WALS Abbreviations
-- ============================================================================

private abbrev ch92  := Core.WALS.F92A.allData
private abbrev ch93  := Core.WALS.F93A.allData
private abbrev ch116 := Core.WALS.F116A.allData

-- ============================================================================
-- WALS Local Types
-- ============================================================================

/-- WALS Ch 92A: Position of polar question particles. -/
inductive QParticlePosition where
  | initial         -- Particle precedes clause
  | final           -- Particle follows clause
  | secondPosition  -- Particle in second (Wackernagel) position
  | otherPosition   -- Other position
  | eitherOfTwo     -- In either of two positions
  | noParticle      -- No question particle
  deriving DecidableEq, Repr

/-- WALS Ch 93A: Position of interrogative phrases (wh-words). -/
inductive WhMovementStrategy where
  | initial   -- Wh-phrase obligatorily fronted (wh-movement)
  | inSitu    -- Wh-phrase stays in situ
  | mixed     -- Both strategies available
  deriving DecidableEq, Repr

/-- WALS Ch 116A: How polar questions are formed. -/
inductive PolarQuestionStrategy where
  | particle                  -- Question particle
  | verbMorphology            -- Interrogative verb morphology
  | particleOrMorphology      -- Mixture of particle and verb morphology
  | wordOrder                 -- Interrogative word order (e.g., subject-aux inversion)
  | absenceOfDeclarative      -- Absence of declarative morphemes
  | intonationOnly            -- Interrogative intonation only
  | noDistinction             -- No interrogative-declarative distinction
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

private def fromWALS92A : Core.WALS.F92A.PositionOfPolarQuestionParticles → QParticlePosition
  | .initial               => .initial
  | .final                 => .final
  | .secondPosition        => .secondPosition
  | .otherPosition         => .otherPosition
  | .inEitherOfTwoPositions => .eitherOfTwo
  | .noQuestionParticle    => .noParticle

private def fromWALS93A : Core.WALS.F93A.PositionOfInterrogativePhrasesInContentQuestions → WhMovementStrategy
  | .initialInterrogativePhrase    => .initial
  | .notInitialInterrogativePhrase => .inSitu
  | .mixed                         => .mixed

private def fromWALS116A : Core.WALS.F116A.PolarQuestionType → PolarQuestionStrategy
  | .questionParticle                     => .particle
  | .interrogativeVerbMorphology          => .verbMorphology
  | .mixtureOfPreviousTwoTypes            => .particleOrMorphology
  | .interrogativeWordOrder               => .wordOrder
  | .absenceOfDeclarativeMorphemes        => .absenceOfDeclarative
  | .interrogativeIntonationOnly          => .intonationOnly
  | .noInterrogativeDeclarativeDistinction => .noDistinction

-- ============================================================================
-- WALS Distribution Totals
-- ============================================================================

theorem ch92_total  : ch92.length  = 884 := by native_decide
theorem ch93_total  : ch93.length  = 902 := by native_decide
theorem ch116_total : ch116.length = 955 := by native_decide

-- ============================================================================
-- WALS Question Profile
-- ============================================================================

/-- A language's question-formation profile across WALS Chapters 92A, 93A, 116A. -/
structure QuestionProfile where
  /-- Language name. -/
  language : String
  /-- WALS language code. -/
  walsCode : String
  /-- Ch 92A: Position of polar question particles. -/
  qParticlePos : Option QParticlePosition := none
  /-- Ch 93A: Wh-phrase position in content questions. -/
  whMovement : Option WhMovementStrategy := none
  /-- Ch 116A: Strategy for forming polar questions. -/
  polarStrategy : Option PolarQuestionStrategy := none
  deriving Repr

def english_qProfile : QuestionProfile :=
  { language := "English", walsCode := "eng"
  , qParticlePos := some .noParticle
  , whMovement := some .initial
  , polarStrategy := some .wordOrder }

def hindi_qProfile : QuestionProfile :=
  { language := "Hindi", walsCode := "hin"
  , qParticlePos := some .initial
  , whMovement := some .inSitu
  , polarStrategy := some .particle }

def japanese_qProfile : QuestionProfile :=
  { language := "Japanese", walsCode := "jpn"
  , qParticlePos := some .final
  , whMovement := some .inSitu
  , polarStrategy := some .particle }

def italian_qProfile : QuestionProfile :=
  { language := "Italian", walsCode := "ita"
  , qParticlePos := some .noParticle
  , whMovement := none  -- Italian not in WALS Ch 93A sample
  , polarStrategy := some .intonationOnly }

def newari_qProfile : QuestionProfile :=
  { language := "Newari (Kathmandu)", walsCode := "new"
  , qParticlePos := some .final
  , whMovement := some .inSitu
  , polarStrategy := some .particle }

def allQuestionProfiles : List QuestionProfile :=
  [english_qProfile, hindi_qProfile, japanese_qProfile,
   italian_qProfile, newari_qProfile]

-- ============================================================================
-- WALS Grounding: Ch 92A (Position of Polar Question Particles)
-- ============================================================================

theorem english_ch92 :
    (Core.WALS.F92A.lookup "eng").map (fromWALS92A ·.value) =
      english_qProfile.qParticlePos := by
  native_decide
theorem hindi_ch92 :
    (Core.WALS.F92A.lookup "hin").map (fromWALS92A ·.value) =
      hindi_qProfile.qParticlePos := by
  native_decide
theorem japanese_ch92 :
    (Core.WALS.F92A.lookup "jpn").map (fromWALS92A ·.value) =
      japanese_qProfile.qParticlePos := by
  native_decide
theorem italian_ch92 :
    (Core.WALS.F92A.lookup "ita").map (fromWALS92A ·.value) =
      italian_qProfile.qParticlePos := by
  native_decide
theorem newari_ch92 :
    (Core.WALS.F92A.lookup "new").map (fromWALS92A ·.value) =
      newari_qProfile.qParticlePos := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 93A (Position of Interrogative Phrases)
-- Not all languages are in Ch 93A sample (Italian absent)
-- ============================================================================

theorem english_ch93 :
    (Core.WALS.F93A.lookup "eng").map (fromWALS93A ·.value) =
      english_qProfile.whMovement := by
  native_decide
theorem hindi_ch93 :
    (Core.WALS.F93A.lookup "hin").map (fromWALS93A ·.value) =
      hindi_qProfile.whMovement := by
  native_decide
theorem japanese_ch93 :
    (Core.WALS.F93A.lookup "jpn").map (fromWALS93A ·.value) =
      japanese_qProfile.whMovement := by
  native_decide
theorem newari_ch93 :
    (Core.WALS.F93A.lookup "new").map (fromWALS93A ·.value) =
      newari_qProfile.whMovement := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 116A (Polar Questions)
-- ============================================================================

theorem english_ch116 :
    (Core.WALS.F116A.lookup "eng").map (fromWALS116A ·.value) =
      english_qProfile.polarStrategy := by
  native_decide
theorem hindi_ch116 :
    (Core.WALS.F116A.lookup "hin").map (fromWALS116A ·.value) =
      hindi_qProfile.polarStrategy := by
  native_decide
theorem japanese_ch116 :
    (Core.WALS.F116A.lookup "jpn").map (fromWALS116A ·.value) =
      japanese_qProfile.polarStrategy := by
  native_decide
theorem italian_ch116 :
    (Core.WALS.F116A.lookup "ita").map (fromWALS116A ·.value) =
      italian_qProfile.polarStrategy := by
  native_decide
theorem newari_ch116 :
    (Core.WALS.F116A.lookup "new").map (fromWALS116A ·.value) =
      newari_qProfile.polarStrategy := by
  native_decide

end Phenomena.Questions.Typology

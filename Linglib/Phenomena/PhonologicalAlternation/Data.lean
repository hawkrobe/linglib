/-!
# Phonological Alternation Data

Theory-neutral empirical observations of phonological alternations.
Each datum records an underlying/surface form pair with the alternation
type and environmental context, without committing to any particular
phonological framework (SPE, OT, etc.).
-/

namespace Phenomena.PhonologicalAlternation

-- ============================================================================
-- § 1: Types
-- ============================================================================

/-- Classification of phonological alternation. -/
inductive AlternationType where
  /-- Segment changes one or more feature values. -/
  | featureChange
  /-- Segment is deleted from the string. -/
  | deletion
  /-- Segment is inserted into the string. -/
  | insertion
  deriving DecidableEq, BEq, Repr

/-- A single observed phonological alternation. -/
structure AlternationDatum where
  language : String
  name : String
  description : String
  underlyingForm : String
  surfaceForm : String
  environment : String
  alternationType : AlternationType
  deriving Repr

-- ============================================================================
-- § 2: English Alternations
-- ============================================================================

/-- English preglottalization: voiceless stops become glottalized word-finally.
    /kæt/ → [kætˀ] -/
def englishPreglottalization : AlternationDatum where
  language := "English"
  name := "Preglottalization"
  description := "Voiceless stops acquire glottal constriction word-finally"
  underlyingForm := "kæt"
  surfaceForm := "kætˀ"
  environment := "word-final position"
  alternationType := .featureChange

/-- English postnasal /t/ deletion: voiceless coronal stops delete
    between a nasal and a vowel.
    /wɪntər/ → [wɪnər] -/
def englishPostnasalDeletion : AlternationDatum where
  language := "English"
  name := "Postnasal /t/ Deletion"
  description := "Voiceless coronal stop deletes after nasal before vowel"
  underlyingForm := "wɪntər"
  surfaceForm := "wɪnər"
  environment := "after nasal, before vowel"
  alternationType := .deletion

-- ============================================================================
-- § 3: Korean Alternations
-- ============================================================================

/-- Korean stop nasalization: non-affricate stops become nasals before
    nasal consonants.
    /pakmul/ → [paŋmul] -/
def koreanStopNasalization : AlternationDatum where
  language := "Korean"
  name := "Stop Nasalization"
  description := "Non-affricate stops nasalize before nasal consonants"
  underlyingForm := "pakmul"
  surfaceForm := "paŋmul"
  environment := "before nasal consonant"
  alternationType := .featureChange

-- ============================================================================
-- § 4: English Nasal Place Assimilation
-- ============================================================================

/-- English nasal place assimilation (velar): /n/ → [ŋ] before /k/.
    /ɪnk/ → [ɪŋk] (e.g., "ink") -/
def englishNasalPlaceAssimilation_nk : AlternationDatum where
  language := "English"
  name := "Nasal Place Assimilation (velar)"
  description := "Alveolar nasal assimilates to velar place before velar stop"
  underlyingForm := "nk"
  surfaceForm := "ŋk"
  environment := "nasal before velar stop"
  alternationType := .featureChange

/-- English nasal place assimilation (labial): /n/ → [m] before /p/.
    /ɪnp/ → [ɪmp] (e.g., "input") -/
def englishNasalPlaceAssimilation_np : AlternationDatum where
  language := "English"
  name := "Nasal Place Assimilation (labial)"
  description := "Alveolar nasal assimilates to labial place before labial stop"
  underlyingForm := "np"
  surfaceForm := "mp"
  environment := "nasal before labial stop"
  alternationType := .featureChange

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- All three alternations are classified correctly. -/
theorem preglottalization_is_feature_change :
    englishPreglottalization.alternationType = .featureChange := rfl

theorem postnasal_deletion_is_deletion :
    englishPostnasalDeletion.alternationType = .deletion := rfl

theorem korean_nasalization_is_feature_change :
    koreanStopNasalization.alternationType = .featureChange := rfl

end Phenomena.PhonologicalAlternation

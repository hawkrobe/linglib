import Linglib.Datasets.WALS.Features.F1A
import Linglib.Datasets.WALS.Features.F2A
import Linglib.Datasets.WALS.Features.F3A
import Linglib.Datasets.WALS.Features.F4A
import Linglib.Datasets.WALS.Features.F5A
import Linglib.Datasets.WALS.Features.F6A
import Linglib.Datasets.WALS.Features.F7A
import Linglib.Datasets.WALS.Features.F8A
import Linglib.Datasets.WALS.Features.F9A
import Linglib.Datasets.WALS.Features.F10A
import Linglib.Datasets.WALS.Features.F10B
import Linglib.Datasets.WALS.Features.F11A
import Linglib.Datasets.WALS.Features.F12A
import Linglib.Datasets.WALS.Features.F13A
import Linglib.Datasets.WALS.Features.F14A
import Linglib.Datasets.WALS.Features.F15A
import Linglib.Datasets.WALS.Features.F16A
import Linglib.Datasets.WALS.Features.F17A
import Linglib.Datasets.WALS.Features.F18A
import Linglib.Datasets.WALS.Features.F19A

/-!
# Phonological Typology (WALS Chapters 1--19)
@cite{dryer-haspelmath-2013} @cite{maddieson-2013}

Formalizes the phonological inventory and prosodic typology chapters from
the World Atlas of Language Structures (WALS), covering:

- **Segmental inventory** (Ch 1--8, 18--19): Consonant and vowel inventory size,
  consonant-to-vowel ratio, voicing contrasts, and the presence/absence of
  specific consonant types (uvulars, glottalized consonants, laterals, the
  velar nasal, uncommon consonants like clicks and labial-velars).

- **Vowel features** (Ch 10--11): Vowel nasalization contrasts,
  nasal vowels in West Africa (Ch 10B), and front rounded vowels.

- **Syllable structure** (Ch 12): Simple, moderately complex, or complex.

- **Prosody** (Ch 13--17): Tone systems, fixed vs. free stress location,
  weight-sensitive stress (Ch 15A), weight factors (Ch 16A), and
  rhythmic type (trochaic vs. iambic).

The 19 WALS features are captured in a single `PhonProfile` structure.
Chapters 5, 10B, 15, and 16 are omitted from the profile as they are
sub-classifications of other chapters, but their generated data is
available via converter functions, grounding theorems, and distribution
theorems.
-/

namespace Phenomena.Phonology

-- ============================================================================
-- WALS Generated Data References
-- ============================================================================

private abbrev ch1  := Datasets.WALS.F1A.allData
private abbrev ch2  := Datasets.WALS.F2A.allData
private abbrev ch3  := Datasets.WALS.F3A.allData
private abbrev ch4  := Datasets.WALS.F4A.allData
private abbrev ch5  := Datasets.WALS.F5A.allData
private abbrev ch6  := Datasets.WALS.F6A.allData
private abbrev ch7  := Datasets.WALS.F7A.allData
private abbrev ch8  := Datasets.WALS.F8A.allData
private abbrev ch9  := Datasets.WALS.F9A.allData
private abbrev ch10  := Datasets.WALS.F10A.allData
private abbrev ch10b := Datasets.WALS.F10B.allData
private abbrev ch11  := Datasets.WALS.F11A.allData
private abbrev ch12 := Datasets.WALS.F12A.allData
private abbrev ch13 := Datasets.WALS.F13A.allData
private abbrev ch14  := Datasets.WALS.F14A.allData
private abbrev ch15  := Datasets.WALS.F15A.allData
private abbrev ch16  := Datasets.WALS.F16A.allData
private abbrev ch17  := Datasets.WALS.F17A.allData
private abbrev ch18 := Datasets.WALS.F18A.allData
private abbrev ch19 := Datasets.WALS.F19A.allData

-- ============================================================================
-- Profile Types
-- ============================================================================

/-- Consonant inventory size (WALS Ch 1). -/
inductive CInventorySize where
  | small | moderatelySmall | average | moderatelyLarge | large
  deriving DecidableEq, Repr

/-- Vowel quality inventory size (WALS Ch 2). -/
inductive VInventorySize where
  | small | average | large
  deriving DecidableEq, Repr

/-- Consonant-to-vowel ratio (WALS Ch 3). -/
inductive CVRatio where
  | low | moderatelyLow | average | moderatelyHigh | high
  deriving DecidableEq, Repr

/-- Voicing contrast in obstruents (WALS Ch 4). -/
inductive VoicingContrast where
  | none | plosivesOnly | fricativesOnly | both
  deriving DecidableEq, Repr

/-- Uvular consonant inventory (WALS Ch 6). -/
inductive UvularPresence where
  | none | stopsOnly | continuantsOnly | stopsAndContinuants
  deriving DecidableEq, Repr

/-- Glottalized consonant types (WALS Ch 7). -/
inductive GlottalizedType where
  | none | ejectivesOnly | implosivesOnly | resonantsOnly
  | ejectivesAndImplosives | ejectivesAndResonants
  | implosivesAndResonants | allThree
  deriving DecidableEq, Repr

/-- Lateral consonant inventory (WALS Ch 8). -/
inductive LateralType where
  | noLaterals | lOnly | lateralsNoL | lAndObstruent | obstruentOnly
  deriving DecidableEq, Repr

/-- Velar nasal status (WALS Ch 9). -/
inductive VelarNasalStatus where
  | initial | noInitial | absent
  deriving DecidableEq, Repr

/-- Nasal vowel contrast type in West Africa (WALS Ch 10B).
Areal sub-feature of Ch 10A, covering 40 West African languages. -/
inductive NasalVowelWA where
  | noContrast
  | twoWayNoSpreading | twoWaySpreading
  | fourWayNoSpreading | fourWaySpreading
  deriving DecidableEq, Repr

/-- Front rounded vowel inventory (WALS Ch 11). -/
inductive FrontRounded where
  | none | highAndMid | highOnly | midOnly
  deriving DecidableEq, Repr

/-- Syllable structure complexity (WALS Ch 12). -/
inductive SyllableComplexity where
  | simple | moderatelyComplex | complex
  deriving DecidableEq, Repr

/-- Tone system type (WALS Ch 13). -/
inductive ToneSystem where
  | none | simple | complex
  deriving DecidableEq, Repr

/-- Fixed stress location (WALS Ch 14). -/
inductive StressLocation where
  | noFixed | initial | second | third | antepenultimate | penultimate | ultimate
  deriving DecidableEq, Repr

/-- Weight-sensitive stress pattern (WALS Ch 15A).
Sub-feature of Ch 14A, classifying how stress interacts with syllable weight. -/
inductive WeightStress where
  | leftEdge | leftOriented
  | rightEdge | rightOriented
  | unbounded | combinedRightUnbounded
  | notPredictable | fixedNoWeight
  deriving DecidableEq, Repr

/-- Weight factor in weight-sensitive stress (WALS Ch 16A).
Sub-feature of Ch 14A, classifying what makes a syllable heavy. -/
inductive WeightFactor where
  | noWeight | longVowel | codaConsonant | longVowelOrCoda
  | prominence | lexicalStress | combined
  deriving DecidableEq, Repr

/-- Rhythmic type (WALS Ch 17). -/
inductive RhythmType where
  | trochaic | iambic | dual | undetermined | noRhythm
  deriving DecidableEq, Repr

/-- Missing common consonants (WALS Ch 18). -/
inductive MissingCommon where
  | allPresent | noBilabials | noFricatives | noNasals
  | noBilabialsOrNasals | noFricativesOrNasals
  deriving DecidableEq, Repr

/-- Presence of uncommon consonants (WALS Ch 19). -/
inductive UncommonPresent where
  | none | clicks | labialVelars | pharyngeals | thSounds
  | clicksPharyngealsAndTh | pharyngealsAndTh
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

private def fromWALS1A : Datasets.WALS.F1A.ConsonantInventories → CInventorySize
  | .small           => .small
  | .moderatelySmall => .moderatelySmall
  | .average         => .average
  | .moderatelyLarge => .moderatelyLarge
  | .large           => .large

private def fromWALS2A : Datasets.WALS.F2A.VowelQualityInventories → VInventorySize
  | .small   => .small
  | .average => .average
  | .large   => .large

private def fromWALS3A : Datasets.WALS.F3A.ConsonantVowelRatio → CVRatio
  | .low            => .low
  | .moderatelyLow  => .moderatelyLow
  | .average        => .average
  | .moderatelyHigh => .moderatelyHigh
  | .high           => .high

private def fromWALS4A : Datasets.WALS.F4A.VoicingInPlosivesAndFricatives → VoicingContrast
  | .noVoicingContrast           => .none
  | .inPlosivesAlone             => .plosivesOnly
  | .inFricativesAlone           => .fricativesOnly
  | .inBothPlosivesAndFricatives => .both

private def fromWALS6A : Datasets.WALS.F6A.UvularConsonants → UvularPresence
  | .none                       => .none
  | .uvularStopsOnly            => .stopsOnly
  | .uvularContinuantsOnly      => .continuantsOnly
  | .uvularStopsAndContinuants  => .stopsAndContinuants

private def fromWALS7A : Datasets.WALS.F7A.GlottalizedConsonants → GlottalizedType
  | .noGlottalizedConsonants        => .none
  | .ejectivesOnly                  => .ejectivesOnly
  | .implosivesOnly                 => .implosivesOnly
  | .glottalizedResonantsOnly       => .resonantsOnly
  | .ejectivesAndImplosives         => .ejectivesAndImplosives
  | .ejectivesAndGlottalizedResonants => .ejectivesAndResonants
  | .implosivesAndGlottalizedResonants => .implosivesAndResonants
  | .ejectivesImplosivesAndGlottalizedResonants => .allThree

private def fromWALS8A : Datasets.WALS.F8A.LateralConsonants → LateralType
  | .noLaterals                              => .noLaterals
  | .lNoObstruentLaterals                    => .lOnly
  | .lateralsButNoLNoObstruentLaterals       => .lateralsNoL
  | .lAndLateralObstruent                    => .lAndObstruent
  | .noLButLateralObstruents                 => .obstruentOnly

private def fromWALS9A : Datasets.WALS.F9A.VelarNasal → VelarNasalStatus
  | .initialVelarNasal   => .initial
  | .noInitialVelarNasal => .noInitial
  | .noVelarNasal        => .absent

private def fromWALS10B : Datasets.WALS.F10B.NasalVowelsInWestAfrica → NasalVowelWA
  | .noNasalVsOralVowelContrast                                  => .noContrast
  | .twoWayNasalVsOralVowelContrastWithoutNasalSpreading         => .twoWayNoSpreading
  | .twoWayNasalVsOralVowelContrastWithNasalSpreading            => .twoWaySpreading
  | .fourWayNasalVsOralVowelContrastWithoutNasalSpreading        => .fourWayNoSpreading
  | .fourWayNasalVsOralVowelContrastWithNasalSpreading           => .fourWaySpreading

private def fromWALS11A : Datasets.WALS.F11A.FrontRoundedVowels → FrontRounded
  | .none       => .none
  | .highAndMid => .highAndMid
  | .highOnly   => .highOnly
  | .midOnly    => .midOnly

private def fromWALS12A : Datasets.WALS.F12A.SyllableStructure → SyllableComplexity
  | .simple            => .simple
  | .moderatelyComplex => .moderatelyComplex
  | .complex           => .complex

private def fromWALS13A : Datasets.WALS.F13A.Tone → ToneSystem
  | .noTones          => .none
  | .simpleToneSystem => .simple
  | .complexToneSystem => .complex

private def fromWALS14A : Datasets.WALS.F14A.FixedStressLocations → StressLocation
  | .noFixedStress   => .noFixed
  | .initial         => .initial
  | .second          => .second
  | .third           => .third
  | .antepenultimate => .antepenultimate
  | .penultimate     => .penultimate
  | .ultimate        => .ultimate

private def fromWALS15A : Datasets.WALS.F15A.WeightSensitiveStress → WeightStress
  | .leftEdgeFirstOrSecond           => .leftEdge
  | .leftOrientedOneOfTheFirstThree  => .leftOriented
  | .rightEdgeUltimateOrPenultimate  => .rightEdge
  | .rightOrientedOneOfTheLastThree  => .rightOriented
  | .unboundedStressCanBeAnywhere    => .unbounded
  | .combinedRightEdgeAndUnbounded   => .combinedRightUnbounded
  | .notPredictable                  => .notPredictable
  | .fixedStress                     => .fixedNoWeight

private def fromWALS16A : Datasets.WALS.F16A.WeightFactorsInWeightSensitiveStressSystems → WeightFactor
  | .noWeight                  => .noWeight
  | .longVowel                 => .longVowel
  | .codaConsonant             => .codaConsonant
  | .longVowelOrCodaConsonant  => .longVowelOrCoda
  | .prominence                => .prominence
  | .lexicalStress             => .lexicalStress
  | .combined                  => .combined

private def fromWALS17A : Datasets.WALS.F17A.RhythmTypes → RhythmType
  | .trochaic                       => .trochaic
  | .iambic                         => .iambic
  | .dualBothTrochaicAndIambic      => .dual
  | .undetermined                   => .undetermined
  | .noRhythmicStress               => .noRhythm

private def fromWALS18A : Datasets.WALS.F18A.AbsenceOfCommonConsonants → MissingCommon
  | .allPresent           => .allPresent
  | .noBilabials          => .noBilabials
  | .noFricatives         => .noFricatives
  | .noNasals             => .noNasals
  | .noBilabialsOrNasals  => .noBilabialsOrNasals
  | .noFricativesOrNasals => .noFricativesOrNasals

private def fromWALS19A : Datasets.WALS.F19A.PresenceOfUncommonConsonants → UncommonPresent
  | .none              => .none
  | .clicks            => .clicks
  | .labialVelars      => .labialVelars
  | .pharyngeals       => .pharyngeals
  | .thSounds          => .thSounds
  | .clicksPharyngealsAndTh        => .clicksPharyngealsAndTh
  | .pharyngealsAndTh              => .pharyngealsAndTh

-- ============================================================================
-- PhonProfile
-- ============================================================================

/-- A language's phonological inventory and prosodic profile.

Combines 16 WALS features into a single record. Optional fields
are used where a language may lack data for that chapter. -/
structure PhonProfile where
  -- Segmental inventory (Ch 1--4, 6--8)
  cInventory    : CInventorySize      -- Ch 1A
  vInventory    : VInventorySize      -- Ch 2A
  cvRatio       : CVRatio             -- Ch 3A
  voicing       : VoicingContrast     -- Ch 4A
  uvulars       : UvularPresence      -- Ch 6A
  glottalized   : GlottalizedType     -- Ch 7A
  laterals      : LateralType         -- Ch 8A
  -- Vowel features (Ch 9--11)
  velarNasal    : Option VelarNasalStatus  -- Ch 9A (not all languages surveyed)
  nasalVowels   : Option Bool              -- Ch 10A
  frontRounded  : FrontRounded             -- Ch 11A
  -- Syllable structure (Ch 12)
  syllables     : SyllableComplexity  -- Ch 12A
  -- Prosody (Ch 13--14, 17)
  tone          : ToneSystem          -- Ch 13A
  stress        : Option StressLocation    -- Ch 14A (not all languages surveyed)
  rhythm        : Option RhythmType        -- Ch 17A
  -- Marked segments (Ch 18--19)
  missingCommon : MissingCommon       -- Ch 18A
  uncommon      : UncommonPresent     -- Ch 19A
  deriving DecidableEq, Repr

-- ============================================================================
-- Language Profiles
-- ============================================================================

def english : PhonProfile where
  cInventory    := .average
  vInventory    := .large
  cvRatio       := .low
  voicing       := .both
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .noInitial
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .complex
  tone          := .none
  stress        := some .noFixed
  rhythm        := some .trochaic
  missingCommon := .allPresent
  uncommon      := .thSounds

def german : PhonProfile where
  cInventory    := .average
  vInventory    := .large
  cvRatio       := .low
  voicing       := .both
  uvulars       := .continuantsOnly
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .noInitial
  nasalVowels   := some false
  frontRounded  := .highAndMid
  syllables     := .complex
  tone          := .none
  stress        := some .noFixed
  rhythm        := some .trochaic
  missingCommon := .allPresent
  uncommon      := .none

def finnish : PhonProfile where
  cInventory    := .moderatelySmall
  vInventory    := .large
  cvRatio       := .moderatelyLow
  voicing       := .both
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .noInitial
  nasalVowels   := some false
  frontRounded  := .highAndMid
  syllables     := .moderatelyComplex
  tone          := .none
  stress        := some .initial
  rhythm        := some .trochaic
  missingCommon := .allPresent
  uncommon      := .none

def turkish : PhonProfile where
  cInventory    := .average
  vInventory    := .large
  cvRatio       := .average
  voicing       := .both
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .absent
  nasalVowels   := some false
  frontRounded  := .highAndMid
  syllables     := .moderatelyComplex
  tone          := .none
  stress        := some .noFixed
  rhythm        := some .noRhythm
  missingCommon := .allPresent
  uncommon      := .none

def russian : PhonProfile where
  cInventory    := .moderatelyLarge
  vInventory    := .average
  cvRatio       := .high
  voicing       := .both
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .absent
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .complex
  tone          := .none
  stress        := some .noFixed
  rhythm        := some .noRhythm
  missingCommon := .allPresent
  uncommon      := .none

def french : PhonProfile where
  cInventory    := .average
  vInventory    := .large
  cvRatio       := .low
  voicing       := .both
  uvulars       := .continuantsOnly
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .absent
  nasalVowels   := some true
  frontRounded  := .highAndMid
  syllables     := .complex
  tone          := .none
  stress        := some .noFixed
  rhythm        := some .undetermined
  missingCommon := .allPresent
  uncommon      := .none

def spanish : PhonProfile where
  cInventory    := .average
  vInventory    := .average
  cvRatio       := .average
  voicing       := .fricativesOnly
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .absent
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .moderatelyComplex
  tone          := .none
  stress        := some .noFixed
  rhythm        := some .trochaic
  missingCommon := .allPresent
  uncommon      := .thSounds

def japanese : PhonProfile where
  cInventory    := .moderatelySmall
  vInventory    := .average
  cvRatio       := .average
  voicing       := .both
  uvulars       := .continuantsOnly
  glottalized   := .none
  laterals      := .noLaterals
  velarNasal    := some .absent
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .moderatelyComplex
  tone          := .simple
  stress        := none
  rhythm        := none
  missingCommon := .allPresent
  uncommon      := .none

def mandarin : PhonProfile where
  cInventory    := .average
  vInventory    := .average
  cvRatio       := .average
  voicing       := .fricativesOnly
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .noInitial
  nasalVowels   := some false
  frontRounded  := .highOnly
  syllables     := .moderatelyComplex
  tone          := .complex
  stress        := some .noFixed
  rhythm        := none
  missingCommon := .allPresent
  uncommon      := .none

def hindi : PhonProfile where
  cInventory    := .large
  vInventory    := .average
  cvRatio       := .moderatelyHigh
  voicing       := .both
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .absent
  nasalVowels   := some true
  frontRounded  := .none
  syllables     := .complex
  tone          := .none
  stress        := some .noFixed
  rhythm        := none
  missingCommon := .allPresent
  uncommon      := .none

def georgian : PhonProfile where
  cInventory    := .moderatelyLarge
  vInventory    := .average
  cvRatio       := .moderatelyHigh
  voicing       := .both
  uvulars       := .stopsAndContinuants
  glottalized   := .ejectivesOnly
  laterals      := .lateralsNoL
  velarNasal    := some .absent
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .complex
  tone          := .none
  stress        := some .antepenultimate
  rhythm        := some .trochaic
  missingCommon := .allPresent
  uncommon      := .none

def hungarian : PhonProfile where
  cInventory    := .moderatelyLarge
  vInventory    := .large
  cvRatio       := .average
  voicing       := .both
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .absent
  nasalVowels   := some false
  frontRounded  := .highAndMid
  syllables     := .complex
  tone          := .none
  stress        := some .initial
  rhythm        := some .trochaic
  missingCommon := .allPresent
  uncommon      := .none

def swahili : PhonProfile where
  cInventory    := .moderatelyLarge
  vInventory    := .average
  cvRatio       := .moderatelyHigh
  voicing       := .both
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .initial
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .simple
  tone          := .none
  stress        := some .penultimate
  rhythm        := none
  missingCommon := .allPresent
  uncommon      := .thSounds

def yoruba : PhonProfile where
  cInventory    := .moderatelySmall
  vInventory    := .large
  cvRatio       := .moderatelyLow
  voicing       := .plosivesOnly
  uvulars       := .none
  glottalized   := .none
  laterals      := .lOnly
  velarNasal    := some .absent
  nasalVowels   := some true
  frontRounded  := .none
  syllables     := .simple
  tone          := .complex
  stress        := none
  rhythm        := none
  missingCommon := .allPresent
  uncommon      := .labialVelars

def maori : PhonProfile where
  cInventory    := .small
  vInventory    := .average
  cvRatio       := .low
  voicing       := .none
  uvulars       := .none
  glottalized   := .none
  laterals      := .noLaterals
  velarNasal    := some .initial
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .simple
  tone          := .none
  stress        := some .noFixed
  rhythm        := none
  missingCommon := .allPresent
  uncommon      := .none

def zulu : PhonProfile where
  cInventory    := .moderatelyLarge
  vInventory    := .average
  cvRatio       := .high
  voicing       := .fricativesOnly
  uvulars       := .none
  glottalized   := .ejectivesAndImplosives
  laterals      := .lAndObstruent
  velarNasal    := none
  nasalVowels   := some false
  frontRounded  := .none
  syllables     := .moderatelyComplex
  tone          := .simple
  stress        := some .penultimate
  rhythm        := some .trochaic
  missingCommon := .allPresent
  uncommon      := .clicks

-- ============================================================================
-- WALS Grounding Theorems — Ch 1A: Consonant Inventories
-- ============================================================================

section Ch1

theorem english_ch1 :
    (Datasets.WALS.F1A.lookup "eng").map (fromWALS1A ·.value) = some english.cInventory := by
  native_decide

theorem german_ch1 :
    (Datasets.WALS.F1A.lookup "ger").map (fromWALS1A ·.value) = some german.cInventory := by
  native_decide

theorem finnish_ch1 :
    (Datasets.WALS.F1A.lookup "fin").map (fromWALS1A ·.value) = some finnish.cInventory := by
  native_decide

theorem turkish_ch1 :
    (Datasets.WALS.F1A.lookup "tur").map (fromWALS1A ·.value) = some turkish.cInventory := by
  native_decide

theorem russian_ch1 :
    (Datasets.WALS.F1A.lookup "rus").map (fromWALS1A ·.value) = some russian.cInventory := by
  native_decide

theorem french_ch1 :
    (Datasets.WALS.F1A.lookup "fre").map (fromWALS1A ·.value) = some french.cInventory := by
  native_decide

theorem spanish_ch1 :
    (Datasets.WALS.F1A.lookup "spa").map (fromWALS1A ·.value) = some spanish.cInventory := by
  native_decide

theorem japanese_ch1 :
    (Datasets.WALS.F1A.lookup "jpn").map (fromWALS1A ·.value) = some japanese.cInventory := by
  native_decide

theorem mandarin_ch1 :
    (Datasets.WALS.F1A.lookup "mnd").map (fromWALS1A ·.value) = some mandarin.cInventory := by
  native_decide

theorem hindi_ch1 :
    (Datasets.WALS.F1A.lookup "hin").map (fromWALS1A ·.value) = some hindi.cInventory := by
  native_decide

theorem georgian_ch1 :
    (Datasets.WALS.F1A.lookup "geo").map (fromWALS1A ·.value) = some georgian.cInventory := by
  native_decide

theorem hungarian_ch1 :
    (Datasets.WALS.F1A.lookup "hun").map (fromWALS1A ·.value) = some hungarian.cInventory := by
  native_decide

theorem swahili_ch1 :
    (Datasets.WALS.F1A.lookup "swa").map (fromWALS1A ·.value) = some swahili.cInventory := by
  native_decide

theorem yoruba_ch1 :
    (Datasets.WALS.F1A.lookup "yor").map (fromWALS1A ·.value) = some yoruba.cInventory := by
  native_decide

theorem maori_ch1 :
    (Datasets.WALS.F1A.lookup "mao").map (fromWALS1A ·.value) = some maori.cInventory := by
  native_decide

theorem zulu_ch1 :
    (Datasets.WALS.F1A.lookup "zul").map (fromWALS1A ·.value) = some zulu.cInventory := by
  native_decide

end Ch1

-- ============================================================================
-- WALS Grounding Theorems — Ch 2A: Vowel Quality Inventories
-- ============================================================================

section Ch2

theorem english_ch2 :
    (Datasets.WALS.F2A.lookup "eng").map (fromWALS2A ·.value) = some english.vInventory := by
  native_decide

theorem german_ch2 :
    (Datasets.WALS.F2A.lookup "ger").map (fromWALS2A ·.value) = some german.vInventory := by
  native_decide

theorem finnish_ch2 :
    (Datasets.WALS.F2A.lookup "fin").map (fromWALS2A ·.value) = some finnish.vInventory := by
  native_decide

theorem turkish_ch2 :
    (Datasets.WALS.F2A.lookup "tur").map (fromWALS2A ·.value) = some turkish.vInventory := by
  native_decide

theorem russian_ch2 :
    (Datasets.WALS.F2A.lookup "rus").map (fromWALS2A ·.value) = some russian.vInventory := by
  native_decide

theorem french_ch2 :
    (Datasets.WALS.F2A.lookup "fre").map (fromWALS2A ·.value) = some french.vInventory := by
  native_decide

theorem spanish_ch2 :
    (Datasets.WALS.F2A.lookup "spa").map (fromWALS2A ·.value) = some spanish.vInventory := by
  native_decide

theorem japanese_ch2 :
    (Datasets.WALS.F2A.lookup "jpn").map (fromWALS2A ·.value) = some japanese.vInventory := by
  native_decide

theorem mandarin_ch2 :
    (Datasets.WALS.F2A.lookup "mnd").map (fromWALS2A ·.value) = some mandarin.vInventory := by
  native_decide

theorem hindi_ch2 :
    (Datasets.WALS.F2A.lookup "hin").map (fromWALS2A ·.value) = some hindi.vInventory := by
  native_decide

theorem georgian_ch2 :
    (Datasets.WALS.F2A.lookup "geo").map (fromWALS2A ·.value) = some georgian.vInventory := by
  native_decide

theorem hungarian_ch2 :
    (Datasets.WALS.F2A.lookup "hun").map (fromWALS2A ·.value) = some hungarian.vInventory := by
  native_decide

theorem swahili_ch2 :
    (Datasets.WALS.F2A.lookup "swa").map (fromWALS2A ·.value) = some swahili.vInventory := by
  native_decide

theorem yoruba_ch2 :
    (Datasets.WALS.F2A.lookup "yor").map (fromWALS2A ·.value) = some yoruba.vInventory := by
  native_decide

theorem maori_ch2 :
    (Datasets.WALS.F2A.lookup "mao").map (fromWALS2A ·.value) = some maori.vInventory := by
  native_decide

theorem zulu_ch2 :
    (Datasets.WALS.F2A.lookup "zul").map (fromWALS2A ·.value) = some zulu.vInventory := by
  native_decide

end Ch2

-- ============================================================================
-- WALS Grounding Theorems — Ch 3A: Consonant-Vowel Ratio
-- ============================================================================

section Ch3

theorem english_ch3 :
    (Datasets.WALS.F3A.lookup "eng").map (fromWALS3A ·.value) = some english.cvRatio := by
  native_decide

theorem german_ch3 :
    (Datasets.WALS.F3A.lookup "ger").map (fromWALS3A ·.value) = some german.cvRatio := by
  native_decide

theorem finnish_ch3 :
    (Datasets.WALS.F3A.lookup "fin").map (fromWALS3A ·.value) = some finnish.cvRatio := by
  native_decide

theorem russian_ch3 :
    (Datasets.WALS.F3A.lookup "rus").map (fromWALS3A ·.value) = some russian.cvRatio := by
  native_decide

theorem maori_ch3 :
    (Datasets.WALS.F3A.lookup "mao").map (fromWALS3A ·.value) = some maori.cvRatio := by
  native_decide

theorem zulu_ch3 :
    (Datasets.WALS.F3A.lookup "zul").map (fromWALS3A ·.value) = some zulu.cvRatio := by
  native_decide

end Ch3

-- ============================================================================
-- WALS Grounding Theorems — Ch 4A: Voicing Contrast
-- ============================================================================

section Ch4

theorem english_ch4 :
    (Datasets.WALS.F4A.lookup "eng").map (fromWALS4A ·.value) = some english.voicing := by
  native_decide

theorem german_ch4 :
    (Datasets.WALS.F4A.lookup "ger").map (fromWALS4A ·.value) = some german.voicing := by
  native_decide

theorem spanish_ch4 :
    (Datasets.WALS.F4A.lookup "spa").map (fromWALS4A ·.value) = some spanish.voicing := by
  native_decide

theorem mandarin_ch4 :
    (Datasets.WALS.F4A.lookup "mnd").map (fromWALS4A ·.value) = some mandarin.voicing := by
  native_decide

theorem maori_ch4 :
    (Datasets.WALS.F4A.lookup "mao").map (fromWALS4A ·.value) = some maori.voicing := by
  native_decide

theorem yoruba_ch4 :
    (Datasets.WALS.F4A.lookup "yor").map (fromWALS4A ·.value) = some yoruba.voicing := by
  native_decide

end Ch4

-- ============================================================================
-- WALS Grounding Theorems — Ch 6A--8A: Specific Consonant Types
-- ============================================================================

section Ch6_8

theorem english_ch6 :
    (Datasets.WALS.F6A.lookup "eng").map (fromWALS6A ·.value) = some english.uvulars := by
  native_decide

theorem georgian_ch6 :
    (Datasets.WALS.F6A.lookup "geo").map (fromWALS6A ·.value) = some georgian.uvulars := by
  native_decide

theorem french_ch6 :
    (Datasets.WALS.F6A.lookup "fre").map (fromWALS6A ·.value) = some french.uvulars := by
  native_decide

theorem german_ch6 :
    (Datasets.WALS.F6A.lookup "ger").map (fromWALS6A ·.value) = some german.uvulars := by
  native_decide

theorem english_ch7 :
    (Datasets.WALS.F7A.lookup "eng").map (fromWALS7A ·.value) = some english.glottalized := by
  native_decide

theorem georgian_ch7 :
    (Datasets.WALS.F7A.lookup "geo").map (fromWALS7A ·.value) = some georgian.glottalized := by
  native_decide

theorem zulu_ch7 :
    (Datasets.WALS.F7A.lookup "zul").map (fromWALS7A ·.value) = some zulu.glottalized := by
  native_decide

theorem english_ch8 :
    (Datasets.WALS.F8A.lookup "eng").map (fromWALS8A ·.value) = some english.laterals := by
  native_decide

theorem japanese_ch8 :
    (Datasets.WALS.F8A.lookup "jpn").map (fromWALS8A ·.value) = some japanese.laterals := by
  native_decide

theorem maori_ch8 :
    (Datasets.WALS.F8A.lookup "mao").map (fromWALS8A ·.value) = some maori.laterals := by
  native_decide

theorem georgian_ch8 :
    (Datasets.WALS.F8A.lookup "geo").map (fromWALS8A ·.value) = some georgian.laterals := by
  native_decide

theorem zulu_ch8 :
    (Datasets.WALS.F8A.lookup "zul").map (fromWALS8A ·.value) = some zulu.laterals := by
  native_decide

end Ch6_8

-- ============================================================================
-- WALS Grounding Theorems — Ch 11A--13A: Vowels, Syllables, Tone
-- ============================================================================

section Ch11_13

theorem english_ch11 :
    (Datasets.WALS.F11A.lookup "eng").map (fromWALS11A ·.value) = some english.frontRounded := by
  native_decide

theorem finnish_ch11 :
    (Datasets.WALS.F11A.lookup "fin").map (fromWALS11A ·.value) = some finnish.frontRounded := by
  native_decide

theorem hungarian_ch11 :
    (Datasets.WALS.F11A.lookup "hun").map (fromWALS11A ·.value) = some hungarian.frontRounded := by
  native_decide

theorem french_ch11 :
    (Datasets.WALS.F11A.lookup "fre").map (fromWALS11A ·.value) = some french.frontRounded := by
  native_decide

theorem mandarin_ch11 :
    (Datasets.WALS.F11A.lookup "mnd").map (fromWALS11A ·.value) = some mandarin.frontRounded := by
  native_decide

theorem english_ch12 :
    (Datasets.WALS.F12A.lookup "eng").map (fromWALS12A ·.value) = some english.syllables := by
  native_decide

theorem maori_ch12 :
    (Datasets.WALS.F12A.lookup "mao").map (fromWALS12A ·.value) = some maori.syllables := by
  native_decide

theorem swahili_ch12 :
    (Datasets.WALS.F12A.lookup "swa").map (fromWALS12A ·.value) = some swahili.syllables := by
  native_decide

theorem english_ch13 :
    (Datasets.WALS.F13A.lookup "eng").map (fromWALS13A ·.value) = some english.tone := by
  native_decide

theorem mandarin_ch13 :
    (Datasets.WALS.F13A.lookup "mnd").map (fromWALS13A ·.value) = some mandarin.tone := by
  native_decide

theorem yoruba_ch13 :
    (Datasets.WALS.F13A.lookup "yor").map (fromWALS13A ·.value) = some yoruba.tone := by
  native_decide

theorem japanese_ch13 :
    (Datasets.WALS.F13A.lookup "jpn").map (fromWALS13A ·.value) = some japanese.tone := by
  native_decide

theorem zulu_ch13 :
    (Datasets.WALS.F13A.lookup "zul").map (fromWALS13A ·.value) = some zulu.tone := by
  native_decide

end Ch11_13

-- ============================================================================
-- WALS Grounding Theorems — Ch 14A, 17A: Stress and Rhythm
-- ============================================================================

section Ch14_17

theorem english_ch14 :
    (Datasets.WALS.F14A.lookup "eng").map (fromWALS14A ·.value) = some .noFixed := by
  native_decide

theorem finnish_ch14 :
    (Datasets.WALS.F14A.lookup "fin").map (fromWALS14A ·.value) = some .initial := by
  native_decide

theorem hungarian_ch14 :
    (Datasets.WALS.F14A.lookup "hun").map (fromWALS14A ·.value) = some .initial := by
  native_decide

theorem swahili_ch14 :
    (Datasets.WALS.F14A.lookup "swa").map (fromWALS14A ·.value) = some .penultimate := by
  native_decide

theorem georgian_ch14 :
    (Datasets.WALS.F14A.lookup "geo").map (fromWALS14A ·.value) = some .antepenultimate := by
  native_decide

theorem zulu_ch14 :
    (Datasets.WALS.F14A.lookup "zul").map (fromWALS14A ·.value) = some .penultimate := by
  native_decide

theorem english_ch17 :
    (Datasets.WALS.F17A.lookup "eng").map (fromWALS17A ·.value) = some .trochaic := by
  native_decide

theorem turkish_ch17 :
    (Datasets.WALS.F17A.lookup "tur").map (fromWALS17A ·.value) = some .noRhythm := by
  native_decide

theorem russian_ch17 :
    (Datasets.WALS.F17A.lookup "rus").map (fromWALS17A ·.value) = some .noRhythm := by
  native_decide

theorem french_ch17 :
    (Datasets.WALS.F17A.lookup "fre").map (fromWALS17A ·.value) = some .undetermined := by
  native_decide

end Ch14_17

-- ============================================================================
-- WALS Grounding Theorems — Ch 15A: Weight-Sensitive Stress
-- ============================================================================

section Ch15

theorem english_ch15 :
    (Datasets.WALS.F15A.lookup "eng").map (fromWALS15A ·.value) = some .rightOriented := by
  native_decide

theorem german_ch15 :
    (Datasets.WALS.F15A.lookup "ger").map (fromWALS15A ·.value) = some .rightOriented := by
  native_decide

theorem finnish_ch15 :
    (Datasets.WALS.F15A.lookup "fin").map (fromWALS15A ·.value) = some .fixedNoWeight := by
  native_decide

theorem turkish_ch15 :
    (Datasets.WALS.F15A.lookup "tur").map (fromWALS15A ·.value) = some .unbounded := by
  native_decide

theorem russian_ch15 :
    (Datasets.WALS.F15A.lookup "rus").map (fromWALS15A ·.value) = some .unbounded := by
  native_decide

theorem french_ch15 :
    (Datasets.WALS.F15A.lookup "fre").map (fromWALS15A ·.value) = some .rightEdge := by
  native_decide

theorem spanish_ch15 :
    (Datasets.WALS.F15A.lookup "spa").map (fromWALS15A ·.value) = some .rightEdge := by
  native_decide

theorem mandarin_ch15 :
    (Datasets.WALS.F15A.lookup "mnd").map (fromWALS15A ·.value) = some .notPredictable := by
  native_decide

theorem hindi_ch15 :
    (Datasets.WALS.F15A.lookup "hin").map (fromWALS15A ·.value) = some .rightOriented := by
  native_decide

theorem georgian_ch15 :
    (Datasets.WALS.F15A.lookup "geo").map (fromWALS15A ·.value) = some .fixedNoWeight := by
  native_decide

theorem hungarian_ch15 :
    (Datasets.WALS.F15A.lookup "hun").map (fromWALS15A ·.value) = some .fixedNoWeight := by
  native_decide

theorem swahili_ch15 :
    (Datasets.WALS.F15A.lookup "swa").map (fromWALS15A ·.value) = some .fixedNoWeight := by
  native_decide

theorem maori_ch15 :
    (Datasets.WALS.F15A.lookup "mao").map (fromWALS15A ·.value) = some .unbounded := by
  native_decide

theorem zulu_ch15 :
    (Datasets.WALS.F15A.lookup "zul").map (fromWALS15A ·.value) = some .fixedNoWeight := by
  native_decide

end Ch15

-- ============================================================================
-- WALS Grounding Theorems — Ch 16A: Weight Factors
-- ============================================================================

section Ch16

theorem english_ch16 :
    (Datasets.WALS.F16A.lookup "eng").map (fromWALS16A ·.value) = some .longVowelOrCoda := by
  native_decide

theorem german_ch16 :
    (Datasets.WALS.F16A.lookup "ger").map (fromWALS16A ·.value) = some .codaConsonant := by
  native_decide

theorem finnish_ch16 :
    (Datasets.WALS.F16A.lookup "fin").map (fromWALS16A ·.value) = some .noWeight := by
  native_decide

theorem turkish_ch16 :
    (Datasets.WALS.F16A.lookup "tur").map (fromWALS16A ·.value) = some .lexicalStress := by
  native_decide

theorem russian_ch16 :
    (Datasets.WALS.F16A.lookup "rus").map (fromWALS16A ·.value) = some .lexicalStress := by
  native_decide

theorem french_ch16 :
    (Datasets.WALS.F16A.lookup "fre").map (fromWALS16A ·.value) = some .prominence := by
  native_decide

theorem spanish_ch16 :
    (Datasets.WALS.F16A.lookup "spa").map (fromWALS16A ·.value) = some .combined := by
  native_decide

theorem mandarin_ch16 :
    (Datasets.WALS.F16A.lookup "mnd").map (fromWALS16A ·.value) = some .lexicalStress := by
  native_decide

theorem hindi_ch16 :
    (Datasets.WALS.F16A.lookup "hin").map (fromWALS16A ·.value) = some .longVowelOrCoda := by
  native_decide

theorem georgian_ch16 :
    (Datasets.WALS.F16A.lookup "geo").map (fromWALS16A ·.value) = some .noWeight := by
  native_decide

theorem hungarian_ch16 :
    (Datasets.WALS.F16A.lookup "hun").map (fromWALS16A ·.value) = some .longVowel := by
  native_decide

theorem swahili_ch16 :
    (Datasets.WALS.F16A.lookup "swa").map (fromWALS16A ·.value) = some .noWeight := by
  native_decide

theorem maori_ch16 :
    (Datasets.WALS.F16A.lookup "mao").map (fromWALS16A ·.value) = some .longVowel := by
  native_decide

theorem zulu_ch16 :
    (Datasets.WALS.F16A.lookup "zul").map (fromWALS16A ·.value) = some .noWeight := by
  native_decide

end Ch16

-- ============================================================================
-- WALS Grounding Theorems — Ch 18A--19A: Marked Segments
-- ============================================================================

section Ch18_19

theorem english_ch18 :
    (Datasets.WALS.F18A.lookup "eng").map (fromWALS18A ·.value) = some english.missingCommon := by
  native_decide

theorem english_ch19 :
    (Datasets.WALS.F19A.lookup "eng").map (fromWALS19A ·.value) = some english.uncommon := by
  native_decide

theorem spanish_ch19 :
    (Datasets.WALS.F19A.lookup "spa").map (fromWALS19A ·.value) = some spanish.uncommon := by
  native_decide

theorem zulu_ch19 :
    (Datasets.WALS.F19A.lookup "zul").map (fromWALS19A ·.value) = some zulu.uncommon := by
  native_decide

theorem yoruba_ch19 :
    (Datasets.WALS.F19A.lookup "yor").map (fromWALS19A ·.value) = some yoruba.uncommon := by
  native_decide

end Ch18_19

-- ============================================================================
-- Distribution Theorems
-- ============================================================================

/-- Ch 1: Average-sized consonant inventories are most common. -/
theorem ch1_average_modal :
    (ch1.filter (·.value == .average)).length >
    (ch1.filter (·.value == .small)).length ∧
    (ch1.filter (·.value == .average)).length >
    (ch1.filter (·.value == .large)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 2: Average vowel inventories (5--6) are the majority. -/
theorem ch2_average_modal :
    (ch2.filter (·.value == .average)).length >
    (ch2.filter (·.value == .small)).length ∧
    (ch2.filter (·.value == .average)).length >
    (ch2.filter (·.value == .large)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 6: The vast majority of languages lack uvular consonants. -/
theorem ch6_no_uvulars_dominant :
    (ch6.filter (·.value == .none)).length >
    4 * ((ch6.filter (·.value == .uvularStopsOnly)).length +
         (ch6.filter (·.value == .uvularContinuantsOnly)).length +
         (ch6.filter (·.value == .uvularStopsAndContinuants)).length) := by
  native_decide

/-- Ch 7: Most languages lack glottalized consonants. -/
theorem ch7_no_glottalized_dominant :
    (ch7.filter (·.value == .noGlottalizedConsonants)).length >
    ch7.length / 2 := by native_decide

/-- Ch 12: Moderately complex syllable structure is most common. -/
theorem ch12_moderate_modal :
    (ch12.filter (·.value == .moderatelyComplex)).length >
    (ch12.filter (·.value == .simple)).length ∧
    (ch12.filter (·.value == .moderatelyComplex)).length >
    (ch12.filter (·.value == .complex)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 13: More languages lack tone than have it, but tonal languages
    are a substantial minority. -/
theorem ch13_no_tone_plurality :
    (ch13.filter (·.value == .noTones)).length >
    (ch13.filter (·.value == .simpleToneSystem)).length +
    (ch13.filter (·.value == .complexToneSystem)).length := by
  native_decide

/-- Ch 17: Trochaic rhythm is overwhelmingly dominant among languages
    with rhythmic stress. -/
theorem ch17_trochaic_dominant :
    (ch17.filter (·.value == .trochaic)).length >
    4 * (ch17.filter (·.value == .iambic)).length := by
  native_decide

/-- Ch 18: The vast majority of languages have all common consonants
    (bilabials, fricatives, nasals). -/
theorem ch18_all_present_dominant :
    (ch18.filter (·.value == .allPresent)).length > ch18.length * 8 / 10 := by
  native_decide

-- ============================================================================
-- Sample sizes
-- ============================================================================

/-- Ch 10B: Half of the surveyed West African languages lack nasal vowel
    contrasts entirely. -/
theorem ch10b_no_contrast_half :
    (ch10b.filter (·.value == .noNasalVsOralVowelContrast)).length = ch10b.length / 2 := by
  native_decide

/-- Ch 15A: Fixed stress (no weight-sensitivity) is the majority pattern. -/
theorem ch15_fixed_majority :
    (ch15.filter (·.value == .fixedStress)).length > ch15.length / 2 := by
  native_decide

/-- Ch 16A: More than half of languages show no syllable-weight effects
    on stress. -/
theorem ch16_no_weight_majority :
    (ch16.filter (·.value == .noWeight)).length > ch16.length / 2 := by
  native_decide

-- ============================================================================
-- Sample sizes
-- ============================================================================

theorem ch1_total   : ch1.length   = 563 := by native_decide
theorem ch2_total   : ch2.length   = 564 := by native_decide
theorem ch3_total   : ch3.length   = 564 := by native_decide
theorem ch10b_total : ch10b.length =  40 := by native_decide
theorem ch12_total  : ch12.length  = 486 := by native_decide
theorem ch13_total  : ch13.length  = 527 := by native_decide
theorem ch15_total  : ch15.length  = 500 := by native_decide
theorem ch16_total  : ch16.length  = 500 := by native_decide

end Phenomena.Phonology

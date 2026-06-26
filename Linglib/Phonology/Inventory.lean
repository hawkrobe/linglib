import Linglib.Data.WALS.Features.F1A
import Linglib.Data.WALS.Features.F2A
import Linglib.Data.WALS.Features.F3A
import Linglib.Data.WALS.Features.F4A
import Linglib.Data.WALS.Features.F5A
import Linglib.Data.WALS.Features.F6A
import Linglib.Data.WALS.Features.F7A
import Linglib.Data.WALS.Features.F8A
import Linglib.Data.WALS.Features.F9A
import Linglib.Data.WALS.Features.F10A
import Linglib.Data.WALS.Features.F10B
import Linglib.Data.WALS.Features.F11A
import Linglib.Data.WALS.Features.F12A
import Linglib.Data.WALS.Features.F13A
import Linglib.Data.WALS.Features.F14A
import Linglib.Data.WALS.Features.F15A
import Linglib.Data.WALS.Features.F16A
import Linglib.Data.WALS.Features.F17A
import Linglib.Data.WALS.Features.F18A
import Linglib.Data.WALS.Features.F19A

/-!
# Phonological typology — WALS substrate (Chapters 1–19)
[dryer-haspelmath-2013] [maddieson-2013] [hajek-2013] [goedemans-van-der-hulst-2013]

Theory-neutral phonological-typology substrate distilled from WALS Chapters
1–19, in the same `Linglib/Typology/{Domain}.lean` mould as `Case.lean`,
`WordOrder.lean`, etc. Per-chapter enums + WALS converters + WALS aggregate
distributional theorems.

## Authorship attribution (NOT one paper)

The 19 chapters are NOT all by Maddieson — the file's previous incarnation
(`Phenomena/Phonology/Typology.lean`) cited only `[maddieson-2013]`,
which is an attribution error. Correct split:

- **Chs 1–9, 11–13, 18–19**: Maddieson 2013 (segmental inventory + tone)
- **Ch 10 (10A, 10B)**: Hajek 2013 (vowel nasalization, incl. West Africa)
- **Chs 14–17**: Goedemans & van der Hulst 2013 (stress location, weight-
  sensitivity, weight factors, rhythm). Different framework: StressTyp
  database, presupposes a metrical-grid view where every word has a
  primary head — exactly what Hyman 2006 (the file's main consumer)
  challenges.

## Theory-laden chapters (acknowledged)

This file is **substrate** in the sense that it just hosts WALS data; but
several WALS chapters embed analytical commitments worth flagging:

- **Ch 13 (tone) is NOT framework-neutral.** The `noTones / simpleToneSystem
  / complexToneSystem` partition operationalises tone as *level inventory
  size*, exactly the position Hyman 2006 challenges (he defines tone
  *functionally*: "pitch enters lexical realisation"). `Hyman2006.lean`
  collapses the simple/complex split back to a single `+T` bit and flags
  WALS as "coarser than Lionnet 2025".
- **Chs 14–17 (stress) embed StressTyp commitments.** `fixedStress`
  presupposes obligatory metrical heads; languages without word-level
  heads (French in Hyman's analysis) are mis-coded. `Hyman2006.lean`
  records this as `french_wals_mismatch`.
- **Ch 12 (syllable structure) commits to syllable-as-unit.** Languages
  analysed without syllables (Bella Coola per Bagemihl 1991) cannot be
  classified.

These commitments are NOT removed at the substrate level — the substrate
records what WALS encodes, with the commitments. Theory-side critique
lives in study files (`Hyman2006.lean`, future work).

## Featural double-coding (deferred)

WALS Chs 7 (glottalized), 8 (lateral), 9 (velar nasal), 11 (front rounded)
are inventory-presence claims that could derive from the featural substrate
in `Linglib/Phonology/Feature.lean` (`[+constricted
glottis]`, `[+lateral]`, `[+nasal, +dorsal]`, `[+front, +round]`) applied
to a PHOIBLE inventory. Bridge theorems are deferred to
`Studies/Maddieson2013.lean`.

## PHOIBLE 2.0 as the post-2019 successor for inventory facts

Maddieson's UPSID-based methodology (~451 inventories) is the 1980s baseline
WALS Ch 1–11/18–19 inherits. The field-canonical post-2019 successor is
PHOIBLE 2.0 ([moran-mccloy-2019]; ~3000 inventories with full IPA
transcription + 37-feature decomposition), housed in
`Linglib/Data/PHOIBLE/`. WALS partitions remain useful for cross-paper
*classification* references; PHOIBLE provides the underlying inventories.
Bridge theorems WALS↔PHOIBLE live in
`Studies/Maddieson2013.lean`.

-/

set_option autoImplicit false

namespace Phonology.Inventory

private abbrev ch1   := Data.WALS.F1A.allData
private abbrev ch2   := Data.WALS.F2A.allData
private abbrev ch3   := Data.WALS.F3A.allData
private abbrev ch4   := Data.WALS.F4A.allData
private abbrev ch5   := Data.WALS.F5A.allData
private abbrev ch6   := Data.WALS.F6A.allData
private abbrev ch7   := Data.WALS.F7A.allData
private abbrev ch8   := Data.WALS.F8A.allData
private abbrev ch9   := Data.WALS.F9A.allData
private abbrev ch10  := Data.WALS.F10A.allData
private abbrev ch10b := Data.WALS.F10B.allData
private abbrev ch11  := Data.WALS.F11A.allData
private abbrev ch12  := Data.WALS.F12A.allData
private abbrev ch13  := Data.WALS.F13A.allData
private abbrev ch14  := Data.WALS.F14A.allData
private abbrev ch15  := Data.WALS.F15A.allData
private abbrev ch16  := Data.WALS.F16A.allData
private abbrev ch17  := Data.WALS.F17A.allData
private abbrev ch18  := Data.WALS.F18A.allData
private abbrev ch19  := Data.WALS.F19A.allData

-- ============================================================================
-- §1. Per-chapter enums
-- ============================================================================

/-- Consonant inventory size (WALS Ch 1, [maddieson-2013]). -/
inductive CInventorySize where
  | small | moderatelySmall | average | moderatelyLarge | large
  deriving DecidableEq, Repr

/-- Vowel quality inventory size (WALS Ch 2, [maddieson-2013]). -/
inductive VInventorySize where
  | small | average | large
  deriving DecidableEq, Repr

/-- Consonant-to-vowel ratio (WALS Ch 3, [maddieson-2013]). -/
inductive CVRatio where
  | low | moderatelyLow | average | moderatelyHigh | high
  deriving DecidableEq, Repr

/-- Voicing contrast in obstruents (WALS Ch 4, [maddieson-2013]). -/
inductive VoicingContrast where
  | none | plosivesOnly | fricativesOnly | both
  deriving DecidableEq, Repr

/-- Uvular consonant inventory (WALS Ch 6, [maddieson-2013]). -/
inductive UvularPresence where
  | none | stopsOnly | continuantsOnly | stopsAndContinuants
  deriving DecidableEq, Repr

/-- Glottalized consonant types (WALS Ch 7, [maddieson-2013]). Could
    derive from `Phonology/Feature.lean` `[+constricted
    glottis]` applied to a PHOIBLE inventory; bridge in Maddieson2013.lean. -/
inductive GlottalizedType where
  | none | ejectivesOnly | implosivesOnly | resonantsOnly
  | ejectivesAndImplosives | ejectivesAndResonants
  | implosivesAndResonants | allThree
  deriving DecidableEq, Repr

/-- Lateral consonant inventory (WALS Ch 8, [maddieson-2013]).
    Featural duplicate of `[+lateral]`. -/
inductive LateralType where
  | noLaterals | lOnly | lateralsNoL | lAndObstruent | obstruentOnly
  deriving DecidableEq, Repr

/-- Velar nasal status (WALS Ch 9, [maddieson-2013]).
    Featural duplicate of `[+nasal, +dorsal]`. -/
inductive VelarNasalStatus where
  | initial | noInitial | absent
  deriving DecidableEq, Repr

/-- Nasal vowel contrast type in West Africa (WALS Ch 10B,
    [hajek-2013]). Areal sub-feature of Ch 10A. -/
inductive NasalVowelWA where
  | noContrast
  | twoWayNoSpreading | twoWaySpreading
  | fourWayNoSpreading | fourWaySpreading
  deriving DecidableEq, Repr

/-- Front rounded vowel inventory (WALS Ch 11, [maddieson-2013]).
    Featural duplicate of `[+front, +round]`. -/
inductive FrontRounded where
  | none | highAndMid | highOnly | midOnly
  deriving DecidableEq, Repr

/-- Syllable structure complexity (WALS Ch 12, [maddieson-2013]).
    Operationalised as max onset/coda length; commits to syllable-as-unit. -/
inductive SyllableComplexity where
  | simple | moderatelyComplex | complex
  deriving DecidableEq, Repr

/-- Tone system type (WALS Ch 13, [maddieson-2013]).
    **Theory-laden**: defines tone by level-inventory size, which Hyman
    2006 explicitly challenges (functional definition: "pitch enters
    lexical realisation"). Substrate records WALS as-is; functional-tone
    work projects via `Studies/Hyman2006.lean`. -/
inductive ToneSystem where
  | none | simple | complex
  deriving DecidableEq, Repr

/-- Fixed stress location (WALS Ch 14, [goedemans-van-der-hulst-2013]).
    StressTyp framework: presupposes obligatory metrical heads. -/
inductive StressLocation where
  | noFixed | initial | second | third | antepenultimate | penultimate | ultimate
  deriving DecidableEq, Repr

/-- Weight-sensitive stress pattern (WALS Ch 15A,
    [goedemans-van-der-hulst-2013]). Sub-feature of Ch 14A. -/
inductive WeightStress where
  | leftEdge | leftOriented
  | rightEdge | rightOriented
  | unbounded | combinedRightUnbounded
  | notPredictable | fixedNoWeight
  deriving DecidableEq, Repr

/-- Weight factor in weight-sensitive stress (WALS Ch 16A,
    [goedemans-van-der-hulst-2013]). Sub-feature of Ch 14A. -/
inductive WeightFactor where
  | noWeight | longVowel | codaConsonant | longVowelOrCoda
  | prominence | lexicalStress | combined
  deriving DecidableEq, Repr

/-- Rhythmic type (WALS Ch 17, [goedemans-van-der-hulst-2013]). -/
inductive RhythmType where
  | trochaic | iambic | dual | undetermined | noRhythm
  deriving DecidableEq, Repr

/-- Missing common consonants (WALS Ch 18, [maddieson-2013]). -/
inductive MissingCommon where
  | allPresent | noBilabials | noFricatives | noNasals
  | noBilabialsOrNasals | noFricativesOrNasals
  deriving DecidableEq, Repr

/-- Presence of uncommon consonants (WALS Ch 19, [maddieson-2013]). -/
inductive UncommonPresent where
  | none | clicks | labialVelars | pharyngeals | thSounds
  | clicksPharyngealsAndTh | pharyngealsAndTh
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. WALS converter functions
-- ============================================================================

def fromWALS1A : Data.WALS.F1A.ConsonantInventories → CInventorySize
  | .small           => .small
  | .moderatelySmall => .moderatelySmall
  | .average         => .average
  | .moderatelyLarge => .moderatelyLarge
  | .large           => .large

def fromWALS2A : Data.WALS.F2A.VowelQualityInventories → VInventorySize
  | .small   => .small
  | .average => .average
  | .large   => .large

def fromWALS3A : Data.WALS.F3A.ConsonantVowelRatio → CVRatio
  | .low            => .low
  | .moderatelyLow  => .moderatelyLow
  | .average        => .average
  | .moderatelyHigh => .moderatelyHigh
  | .high           => .high

def fromWALS4A : Data.WALS.F4A.VoicingInPlosivesAndFricatives → VoicingContrast
  | .noVoicingContrast           => .none
  | .inPlosivesAlone             => .plosivesOnly
  | .inFricativesAlone           => .fricativesOnly
  | .inBothPlosivesAndFricatives => .both

def fromWALS6A : Data.WALS.F6A.UvularConsonants → UvularPresence
  | .none                       => .none
  | .uvularStopsOnly            => .stopsOnly
  | .uvularContinuantsOnly      => .continuantsOnly
  | .uvularStopsAndContinuants  => .stopsAndContinuants

def fromWALS7A : Data.WALS.F7A.GlottalizedConsonants → GlottalizedType
  | .noGlottalizedConsonants                    => .none
  | .ejectivesOnly                              => .ejectivesOnly
  | .implosivesOnly                             => .implosivesOnly
  | .glottalizedResonantsOnly                   => .resonantsOnly
  | .ejectivesAndImplosives                     => .ejectivesAndImplosives
  | .ejectivesAndGlottalizedResonants           => .ejectivesAndResonants
  | .implosivesAndGlottalizedResonants          => .implosivesAndResonants
  | .ejectivesImplosivesAndGlottalizedResonants => .allThree

def fromWALS8A : Data.WALS.F8A.LateralConsonants → LateralType
  | .noLaterals                              => .noLaterals
  | .lNoObstruentLaterals                    => .lOnly
  | .lateralsButNoLNoObstruentLaterals       => .lateralsNoL
  | .lAndLateralObstruent                    => .lAndObstruent
  | .noLButLateralObstruents                 => .obstruentOnly

def fromWALS9A : Data.WALS.F9A.VelarNasal → VelarNasalStatus
  | .initialVelarNasal   => .initial
  | .noInitialVelarNasal => .noInitial
  | .noVelarNasal        => .absent

def fromWALS10B : Data.WALS.F10B.NasalVowelsInWestAfrica → NasalVowelWA
  | .noNasalVsOralVowelContrast                                  => .noContrast
  | .twoWayNasalVsOralVowelContrastWithoutNasalSpreading         => .twoWayNoSpreading
  | .twoWayNasalVsOralVowelContrastWithNasalSpreading            => .twoWaySpreading
  | .fourWayNasalVsOralVowelContrastWithoutNasalSpreading        => .fourWayNoSpreading
  | .fourWayNasalVsOralVowelContrastWithNasalSpreading           => .fourWaySpreading

def fromWALS11A : Data.WALS.F11A.FrontRoundedVowels → FrontRounded
  | .none       => .none
  | .highAndMid => .highAndMid
  | .highOnly   => .highOnly
  | .midOnly    => .midOnly

def fromWALS12A : Data.WALS.F12A.SyllableStructure → SyllableComplexity
  | .simple            => .simple
  | .moderatelyComplex => .moderatelyComplex
  | .complex           => .complex

def fromWALS13A : Data.WALS.F13A.Tone → ToneSystem
  | .noTones          => .none
  | .simpleToneSystem => .simple
  | .complexToneSystem => .complex

def fromWALS14A : Data.WALS.F14A.FixedStressLocations → StressLocation
  | .noFixedStress   => .noFixed
  | .initial         => .initial
  | .second          => .second
  | .third           => .third
  | .antepenultimate => .antepenultimate
  | .penultimate     => .penultimate
  | .ultimate        => .ultimate

def fromWALS15A : Data.WALS.F15A.WeightSensitiveStress → WeightStress
  | .leftEdgeFirstOrSecond           => .leftEdge
  | .leftOrientedOneOfTheFirstThree  => .leftOriented
  | .rightEdgeUltimateOrPenultimate  => .rightEdge
  | .rightOrientedOneOfTheLastThree  => .rightOriented
  | .unboundedStressCanBeAnywhere    => .unbounded
  | .combinedRightEdgeAndUnbounded   => .combinedRightUnbounded
  | .notPredictable                  => .notPredictable
  | .fixedStress                     => .fixedNoWeight

def fromWALS16A : Data.WALS.F16A.WeightFactorsInWeightSensitiveStressSystems → WeightFactor
  | .noWeight                  => .noWeight
  | .longVowel                 => .longVowel
  | .codaConsonant             => .codaConsonant
  | .longVowelOrCodaConsonant  => .longVowelOrCoda
  | .prominence                => .prominence
  | .lexicalStress             => .lexicalStress
  | .combined                  => .combined

def fromWALS17A : Data.WALS.F17A.RhythmTypes → RhythmType
  | .trochaic                       => .trochaic
  | .iambic                         => .iambic
  | .dualBothTrochaicAndIambic      => .dual
  | .undetermined                   => .undetermined
  | .noRhythmicStress               => .noRhythm

def fromWALS18A : Data.WALS.F18A.AbsenceOfCommonConsonants → MissingCommon
  | .allPresent           => .allPresent
  | .noBilabials          => .noBilabials
  | .noFricatives         => .noFricatives
  | .noNasals             => .noNasals
  | .noBilabialsOrNasals  => .noBilabialsOrNasals
  | .noFricativesOrNasals => .noFricativesOrNasals

def fromWALS19A : Data.WALS.F19A.PresenceOfUncommonConsonants → UncommonPresent
  | .none              => .none
  | .clicks            => .clicks
  | .labialVelars      => .labialVelars
  | .pharyngeals       => .pharyngeals
  | .thSounds          => .thSounds
  | .clicksPharyngealsAndTh        => .clicksPharyngealsAndTh
  | .pharyngealsAndTh              => .pharyngealsAndTh

-- ============================================================================
-- §3. WALS aggregate distributional theorems
-- ============================================================================

/-- Ch 1: Average-sized consonant inventories are most common. -/
theorem ch1_average_modal :
    (ch1.filter (·.value == .average)).length >
    (ch1.filter (·.value == .small)).length ∧
    (ch1.filter (·.value == .average)).length >
    (ch1.filter (·.value == .large)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 2: Average vowel inventories (5–6) are the majority. -/
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
    are a substantial minority. (Maddieson's level-counting partition;
    Hyman 2006 would aggregate `simple + complex` differently.) -/
theorem ch13_no_tone_plurality :
    (ch13.filter (·.value == .noTones)).length >
    (ch13.filter (·.value == .simpleToneSystem)).length +
    (ch13.filter (·.value == .complexToneSystem)).length := by
  native_decide

/-- Ch 17: Trochaic rhythm is overwhelmingly dominant among languages
    with rhythmic stress. **Caveat**: WALS-coding artefact noted by
    Hayes 1995 (uneven trochees inflate the trochaic count). -/
theorem ch17_trochaic_dominant :
    (ch17.filter (·.value == .trochaic)).length >
    4 * (ch17.filter (·.value == .iambic)).length := by
  native_decide

/-- Ch 18: The vast majority of languages have all common consonants
    (bilabials, fricatives, nasals). -/
theorem ch18_all_present_dominant :
    (ch18.filter (·.value == .allPresent)).length > ch18.length * 8 / 10 := by
  native_decide

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


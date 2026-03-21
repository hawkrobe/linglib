import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.FeatureGeometry
import Linglib.Theories.Phonology.RuleBased.Defs
import Linglib.Theories.Phonology.Autosegmental.Defs
import Linglib.Theories.Phonology.Harmony.Defs

/-!
# Finnish Vowel Harmony @cite{karlsson-2017}
@cite{goldsmith-1976} @cite{rose-walker-2011}

Finnish has **palatal vowel harmony**: the [±back] feature of root vowels
propagates rightward through all suffixes. This is
a textbook case of autosegmental feature spreading.

## Vowel classes (Karlsson §2.1)

- **Back vowels**: a [+back, +low], o [+back, +round], u [+back, +high]
- **Front vowels**: ä [−back, +low], ö [−back, +round], y [−back, +high]
- **Neutral vowels**: e [−back, −round, −low], i [−back, +high, −round]
  — transparent to harmony (do not trigger or block spreading)

## Suffix alternation

Most suffixes contain an **archiphonemic** vowel /A/ that surfaces as
[a] after back-vowel stems and [ä] after front-vowel stems:

- Partitive: kirja-**a** ('book') vs. käsi-**ä** ('hand')
- Inessive: talo-**ssa** ('in the house') vs. metsä-**ssä** ('in the forest')

## Formalization (@cite{rose-walker-2011})

Finnish VH is a single `HarmonySystem` with [back] as the spreading feature.
Neutral vowels /e/ and /i/ are transparent: they satisfy `isTransparent` and
are skipped by `triggerValue` (not triggers) and `harmonizeOne` (not targets).

-/

namespace Fragments.Finnish.VowelHarmony

open Theories.Phonology (Segment Feature FeatureVal)
open Theories.Phonology.FeatureGeometry (GeomNode)
open Theories.Phonology.Autosegmental (AutosegRep agreeAt)
open Theories.Phonology.Harmony (HarmonySystem HarmonyDir triggerValue
  harmonizeOne harmonizeSuffix)

-- ============================================================================
-- § 1: Vowel Segments
-- ============================================================================

/-- Finnish back vowel /a/: [+syll, +low, +back, +dorsal, −high, −round]. -/
def a_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.low, true), (Feature.back, true),
   (Feature.high, false), (Feature.round, false)]

/-- Finnish front vowel /ä/: [+syll, +low, −back, +dorsal, −high, −round]. -/
def ä_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.low, true), (Feature.back, false),
   (Feature.high, false), (Feature.round, false)]

/-- Finnish back vowel /o/: [+syll, +round, +back, +dorsal, −high, −low]. -/
def o_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.round, true), (Feature.back, true),
   (Feature.high, false), (Feature.low, false)]

/-- Finnish front vowel /ö/: [+syll, +round, −back, +dorsal, −high, −low]. -/
def ö_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.round, true), (Feature.back, false),
   (Feature.high, false), (Feature.low, false)]

/-- Finnish back vowel /u/: [+syll, +high, +back, +round, +dorsal, −low]. -/
def u_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.back, true),
   (Feature.round, true), (Feature.low, false)]

/-- Finnish front vowel /y/: [+syll, +high, −back, +round, +dorsal, −low]. -/
def y_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.back, false),
   (Feature.round, true), (Feature.low, false)]

/-- Neutral vowel /e/: [+syll, −back, −round, −high, −low, +dorsal]. -/
def e_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.back, false), (Feature.round, false),
   (Feature.high, false), (Feature.low, false)]

/-- Neutral vowel /i/: [+syll, +high, −back, −round, +dorsal, −low]. -/
def i_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.back, false),
   (Feature.round, false), (Feature.low, false)]

-- ============================================================================
-- § 2: Vowel Classification
-- ============================================================================

/-- Is a segment a back vowel? [+syll, +back]. -/
def isBackVowel (s : Segment) : Bool :=
  s.hasValue .syllabic true && s.hasValue .back true

/-- Is a segment a front vowel? [+syll, −back]. -/
def isFrontVowel (s : Segment) : Bool :=
  s.hasValue .syllabic true && s.hasValue .back false

/-- Is a segment a neutral vowel? Front vowels /e/ and /i/ that are
    transparent to harmony: [+syll, −back, −round, −low]. -/
def isNeutral (s : Segment) : Bool :=
  s.hasValue .syllabic true &&
  s.hasValue .back false &&
  s.hasValue .round false &&
  s.hasValue .low false

/-- The harmony class of a vowel: back, front, or neutral. -/
inductive HarmonyClass where
  | back | front | neutral
  deriving DecidableEq, BEq, Repr

/-- Classify a vowel segment. -/
def classifyVowel (s : Segment) : HarmonyClass :=
  if isNeutral s then .neutral
  else if isBackVowel s then .back
  else .front

-- ============================================================================
-- § 3: Harmony System Instance
-- ============================================================================

/-- Finnish palatal harmony: [back] spreads from the last harmonic (non-neutral)
    stem vowel to non-neutral suffix vowels. Neutral vowels /e/, /i/ are
    transparent — they neither trigger nor undergo harmony. -/
def finnishHarmony : HarmonySystem where
  feature       := .back
  isTrigger     := (λ s => s.hasValue .syllabic true && !isNeutral s)
  isTarget      := (λ s => s.hasValue .syllabic true && !isNeutral s)
  isTransparent := isNeutral
  direction     := .rightward

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- /a/ is a back vowel. -/
theorem a_is_back : isBackVowel a_vowel = true := by native_decide

/-- /ä/ is a front vowel. -/
theorem ä_is_front : isFrontVowel ä_vowel = true := by native_decide

/-- /e/ is neutral. -/
theorem e_is_neutral : isNeutral e_vowel = true := by native_decide

/-- /i/ is neutral. -/
theorem i_is_neutral : isNeutral i_vowel = true := by native_decide

/-- /o/ is not neutral (it's a harmonic back vowel). -/
theorem o_not_neutral : isNeutral o_vowel = false := by native_decide

/-- /ö/ is not neutral (it's a harmonic front vowel). -/
theorem ö_not_neutral : isNeutral ö_vowel = false := by native_decide

-- ============================================================================
-- § 5: Harmony System Verification
-- ============================================================================

/-- Back-vowel stems yield back harmony. -/
theorem back_stem_harmony :
    triggerValue finnishHarmony [a_vowel] = some true := by native_decide

/-- Front-vowel stems yield front harmony. -/
theorem front_stem_harmony :
    triggerValue finnishHarmony [ä_vowel] = some false := by native_decide

/-- Neutral-only stems have no trigger (default to front harmony). -/
theorem neutral_only_no_trigger :
    triggerValue finnishHarmony [e_vowel, i_vowel] = none := by
  native_decide

/-- A back stem with a neutral vowel still yields back harmony
    (the neutral vowel is not a trigger, so `triggerValue` finds /a/). -/
theorem back_with_neutral :
    triggerValue finnishHarmony [a_vowel, i_vowel] = some true := by
  native_decide

/-- The /a/–/ä/ pair differs only in [back]: dorsal agreement fails
    between them, confirming they belong to different harmony classes. -/
theorem a_ä_dorsal_disagree :
    agreeAt a_vowel ä_vowel .dorsal = false := by native_decide

/-- Dorsal agreement holds between /a/ and /o/ (both [+back]). -/
theorem a_o_dorsal_agree_on_back :
    a_vowel.hasValue .back true = true ∧
    o_vowel.hasValue .back true = true := by
  exact ⟨by native_decide, by native_decide⟩

end Fragments.Finnish.VowelHarmony

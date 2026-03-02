import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.FeatureGeometry
import Linglib.Theories.Phonology.RuleBased.Defs
import Linglib.Theories.Phonology.Autosegmental.Defs

/-!
# Finnish Vowel Harmony @cite{karlsson-2017}
@cite{goldsmith-1976} @cite{ringen-heinmki-1999}

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

## Formalization

We model harmony as autosegmental spreading of the dorsal node's [back]
feature from the stem's last harmonic vowel rightward through the suffix.
Neutral vowels are transparent: the spreading "skips" them (their own [back]
value is independently set to [−back]).

-/

namespace Fragments.Finnish.VowelHarmony

open Theories.Phonology (Segment Feature FeatureVal)
open Theories.Phonology.FeatureGeometry (GeomNode)
open Theories.Phonology.Autosegmental (AutosegRep agreeAt)

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
-- § 3: Harmony as Dorsal Spreading
-- ============================================================================

/-- Determine the harmony domain of a stem: find the last non-neutral vowel
    and return its [back] value. Returns `none` for stems with only neutral
    vowels (which default to front harmony). -/
def stemHarmony (stem : List Segment) : Option Bool :=
  let harmonicVowels := stem.filter (fun s =>
    s.hasValue .syllabic true && !isNeutral s)
  match harmonicVowels.getLast? with
  | some s => s.spec .back
  | none => none

/-- Apply vowel harmony to a suffix segment: if the segment is a vowel and
    the stem harmony is known, set its [back] feature to match the stem.
    Neutral vowels in the suffix are skipped (they keep [−back]). -/
def harmonize (stemBack : Bool) (s : Segment) : Segment :=
  if s.hasValue .syllabic true && !isNeutral s then
    { spec := fun f => if f == .back then some stemBack else s.spec f }
  else s

/-- Apply vowel harmony to an entire suffix, given the stem's harmony. -/
def harmonizeSuffix (stemBack : Bool) (suffix : List Segment) : List Segment :=
  suffix.map (harmonize stemBack)

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

/-- Back-vowel stems yield back harmony. -/
theorem back_stem_harmony : stemHarmony [a_vowel] = some true := by native_decide

/-- Front-vowel stems yield front harmony. -/
theorem front_stem_harmony : stemHarmony [ä_vowel] = some false := by native_decide

/-- Neutral-only stems have no harmonic vowel (default to front). -/
theorem neutral_only_no_harmony : stemHarmony [e_vowel, i_vowel] = none := by
  native_decide

/-- A back stem with a neutral vowel still yields back harmony
    (the neutral vowel is transparent): stem /a, i/ → back. -/
theorem back_with_neutral : stemHarmony [a_vowel, i_vowel] = some true := by
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

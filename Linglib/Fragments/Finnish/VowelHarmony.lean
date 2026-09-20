import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Segmental.FeatureClass
import Linglib.Phonology.Subregular.LocalRewrite
import Linglib.Phonology.Harmony.System

/-!
# Finnish Vowel Harmony [karlsson-2017]
[goldsmith-1976] [rose-walker-2011]

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

## Formalization ([rose-walker-2011])

Finnish VH is a single `System` with [back] as the spreading feature over the tier of
harmonic vowels: consonants and the neutral vowels /e/ and /i/ are transparent, the
harmonic vowels trigger, a suffix vowel unspecified for [back] is the target, and a stem
with no harmonic vowel takes front suffixes by default.

-/

namespace Finnish.VowelHarmony

open Phonology (Segment Feature FeatureClass)
open Phonology.Harmony (System)

-- ============================================================================
-- § 1: Vowel Segments
-- ============================================================================

/-- The Finnish back vowel /a/ is [+syll, +low, +back, +dorsal, −high, −round]. -/
def a_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.low, true), (Feature.back, true),
   (Feature.high, false), (Feature.round, false)]

/-- The Finnish front vowel /ä/ is [+syll, +low, −back, +dorsal, −high, −round]. -/
def ä_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.low, true), (Feature.back, false),
   (Feature.high, false), (Feature.round, false)]

/-- The Finnish back vowel /o/ is [+syll, +round, +back, +dorsal, −high, −low]. -/
def o_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.round, true), (Feature.back, true),
   (Feature.high, false), (Feature.low, false)]

/-- The Finnish front vowel /ö/ is [+syll, +round, −back, +dorsal, −high, −low]. -/
def ö_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.round, true), (Feature.back, false),
   (Feature.high, false), (Feature.low, false)]

/-- The Finnish back vowel /u/ is [+syll, +high, +back, +round, +dorsal, −low]. -/
def u_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.back, true),
   (Feature.round, true), (Feature.low, false)]

/-- The Finnish front vowel /y/ is [+syll, +high, −back, +round, +dorsal, −low]. -/
def y_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.back, false),
   (Feature.round, true), (Feature.low, false)]

/-- The neutral vowel /e/ is [+syll, −back, −round, −high, −low, +dorsal]. -/
def e_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.back, false), (Feature.round, false),
   (Feature.high, false), (Feature.low, false)]

/-- The neutral vowel /i/ is [+syll, +high, −back, −round, +dorsal, −low]. -/
def i_vowel : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.back, false),
   (Feature.round, false), (Feature.low, false)]

-- ============================================================================
-- § 2: Vowel Classification
-- ============================================================================

/-- The vowel of the alternating suffixes is unspecified for [back], as in the A of the
essive -nA and the partitive -A. -/
def A : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.dorsal, true),
   (Feature.low, true), (Feature.high, false), (Feature.round, false)]

/-- A consonant of the given specifications. -/
private def consonant (specs : List (Feature × Bool)) : Segment :=
  Segment.ofSpecs ((.syllabic, false) :: specs)

def p : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.labial, true), (.voice, false)]
def t : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.coronal, true), (.voice, false)]
def k : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.dorsal, true), (.voice, false)]
def n : Segment := consonant [(.consonantal, true), (.sonorant, true), (.approximant, false),
  (.nasal, true), (.coronal, true), (.voice, true)]
def v : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, true),
  (.labial, true), (.voice, true)]
def l : Segment := consonant [(.consonantal, true), (.sonorant, true), (.lateral, true),
  (.coronal, true), (.voice, true)]
def j : Segment := consonant [(.consonantal, false), (.sonorant, true), (.approximant, true),
  (.continuant, true), (.voice, true)]

/-- Is a segment a back vowel? [+syll, +back]. -/
def isBackVowel (s : Segment) : Bool :=
  s.HasValue .syllabic true && s.HasValue .back true

/-- Is a segment a front vowel? [+syll, −back]. -/
def isFrontVowel (s : Segment) : Bool :=
  s.HasValue .syllabic true && s.HasValue .back false

/-- Is a segment a neutral vowel? Front vowels /e/ and /i/ that are
    transparent to harmony: [+syll, −back, −round, −low]. -/
def isNeutral (s : Segment) : Bool :=
  s.HasValue .syllabic true &&
  s.HasValue .back false &&
  s.HasValue .round false &&
  s.HasValue .low false

/-- The harmony class of a vowel is back, front, or neutral. -/
inductive HarmonyClass where
  | back | front | neutral
  deriving DecidableEq, Repr

/-- Classify a vowel segment. -/
def classifyVowel (s : Segment) : HarmonyClass :=
  if isNeutral s then .neutral
  else if isBackVowel s then .back
  else .front

-- ============================================================================
-- § 3: Harmony System Instance
-- ============================================================================

/-- Finnish palatal harmony spreads [back] from the last harmonic (non-neutral) stem vowel to
the suffix vowels unspecified for it, and a stem with no harmonic vowel takes front suffixes
by default; consonants and the neutral vowels /e/, /i/ are off the tier. -/
def finnishHarmony : System Segment :=
  System.mk' (feature := .back)
    (IsTarget      := fun s => s.HasValue .syllabic true ∧ s .back = none)
    (IsTransparent := fun s => ¬ s.HasValue .syllabic true ∨ isNeutral s = true)
    (direction     := .rightward)
    (default       := some false)

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- /a/ is a back vowel. -/
theorem a_is_back : isBackVowel a_vowel = true := by decide

/-- /ä/ is a front vowel. -/
theorem ä_is_front : isFrontVowel ä_vowel = true := by decide

/-- /e/ is neutral. -/
theorem e_is_neutral : isNeutral e_vowel = true := by decide

/-- /i/ is neutral. -/
theorem i_is_neutral : isNeutral i_vowel = true := by decide

/-- /o/ is not neutral (it's a harmonic back vowel). -/
theorem o_not_neutral : isNeutral o_vowel = false := by decide

/-- /ö/ is not neutral (it's a harmonic front vowel). -/
theorem ö_not_neutral : isNeutral ö_vowel = false := by decide

-- ============================================================================
-- § 5: Harmony System Verification
-- ============================================================================

/-- Back-vowel stems yield back harmony. -/
theorem back_stem_harmony :
    finnishHarmony.searchCopy.sourceValue [a_vowel] = some true := by decide

/-- Front-vowel stems yield front harmony. -/
theorem front_stem_harmony :
    finnishHarmony.searchCopy.sourceValue [ä_vowel] = some false := by decide

/-- Neutral-only stems have no trigger (default to front harmony). -/
theorem neutral_only_no_trigger :
    finnishHarmony.searchCopy.sourceValue [e_vowel, i_vowel] = none := by
  decide

/-- A back stem with a neutral vowel still yields back harmony
    (the neutral vowel is not a trigger, so `triggerValue` finds /a/). -/
theorem back_with_neutral :
    finnishHarmony.searchCopy.sourceValue [a_vowel, i_vowel] = some true := by
  decide

/-- The vowels /a/ and /ä/ differ in [back], so dorsal agreement fails between them and
    they belong to different harmony classes. -/
theorem a_ä_dorsal_disagree : ¬ Set.EqOn a_vowel ä_vowel ↑FeatureClass.dorsal.features := by
  decide

/-- Dorsal agreement holds between /a/ and /o/ (both [+back]). -/
theorem a_o_dorsal_agree_on_back :
    a_vowel.HasValue .back true = true ∧
    o_vowel.HasValue .back true = true := by
  exact ⟨by decide, by decide⟩

end Finnish.VowelHarmony

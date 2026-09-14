import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.Harmony

/-!
# Hungarian vowel harmony

The short vowels of Hungarian as segments, their harmonic classification, and the two harmony
systems the suffix alternations follow: palatal harmony, the backness of the last harmonic
stem vowel spreading rightward through the transparent neutral vowels, and rounding harmony,
the rounding of the last stem vowel, which resolves the three-way suffixes. The seven vowels
are the system (7) of [siptar-torkenczy-2000], with long vowels identical in features since
length is prosodic; the harmonic classification is that of their (27), the front unrounded
vowels being neutral; and the two systems compile the [rose-walker-2011] decomposition to the
substrate's `Harmony.System`.

## Implementation notes

* The short low vowel is phonetically rounded but phonologically [+back, −round, +low].
* Antiharmonic stems, vacillating stems and the height-graded transparency of the neutral
  vowels are not properties of these systems: `Studies/SiptarTorkenczy2000` derives them from
  the book's place-feature analysis.

## References

* [siptar-torkenczy-2000]
* [rose-walker-2011]
-/

namespace Hungarian.VowelHarmony

open Phonology (Segment Feature)
open Subregular.Harmony (System)

/-! ### The vowel inventory -/

/-- /i/, high front unrounded, neutral. -/
def i_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true), (.back, false), (.round, false),
    (.low, false)]

/-- /ü/, high front rounded, front harmonic. -/
def ü_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true), (.back, false), (.round, true),
    (.low, false)]

/-- /u/, high back rounded, back harmonic. -/
def u_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, true), (.back, true), (.round, true),
    (.low, false)]

/-- /e/, mid front unrounded, neutral. -/
def e_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false), (.back, false), (.round, false),
    (.low, false)]

/-- /ö/, mid front rounded, front harmonic. -/
def ö_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false), (.back, false), (.round, true),
    (.low, false)]

/-- /o/, mid back rounded, back harmonic. -/
def o_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false), (.back, true), (.round, true),
    (.low, false)]

/-- /a/, low back unrounded, back harmonic. -/
def a_vowel : Segment := Segment.ofSpecs
  [(.syllabic, true), (.dorsal, true), (.high, false), (.back, true), (.round, false),
    (.low, true)]

/-- The vowel written by an orthographic vowel letter, long and short alike. -/
def ofLetter : String → Option Segment
  | "i" | "í" => some i_vowel
  | "ü" | "ű" => some ü_vowel
  | "u" | "ú" => some u_vowel
  | "e" | "é" => some e_vowel
  | "ö" | "ő" => some ö_vowel
  | "o" | "ó" => some o_vowel
  | "a" | "á" => some a_vowel
  | _ => none

/-- The vowels of a word written as a list of orthographic segments. -/
def vowelsOf (segments : List String) : List Segment := segments.filterMap ofLetter

/-! ### Harmonic classification -/

/-- A vowel is neutral when it is front and unrounded. -/
def isNeutral (s : Segment) : Bool :=
  s.HasValue .syllabic true && s.HasValue .back false && s.HasValue .round false

/-- A vowel is front harmonic when it is front and rounded. -/
def isFrontHarmonic (s : Segment) : Bool :=
  s.HasValue .syllabic true && s.HasValue .back false && s.HasValue .round true

/-- Every back vowel is back harmonic. -/
def isBackHarmonic (s : Segment) : Bool := s.HasValue .syllabic true && s.HasValue .back true

/-! ### The harmony systems -/

/-- Palatal harmony: the backness of the last harmonic stem vowel spreads rightward to the
harmonic suffix vowels, the neutral vowels being transparent. -/
def hungarianPalatalHarmony : System Segment :=
  System.mk' (feature := .back)
    (isTrigger := λ s => s.HasValue .syllabic true && !isNeutral s)
    (isTarget := λ s => s.HasValue .syllabic true && !isNeutral s)
    (isTransparent := isNeutral)
    (direction := .rightward)

/-- Rounding harmony: the rounding of the last stem vowel, with no transparent vowels, which
matters only for front stems since a back stem takes the back alternant of a three-way
suffix. -/
def hungarianLabialHarmony : System Segment :=
  System.mk' (feature := .round)
    (isTrigger := (·.HasValue .syllabic true))
    (isTarget := (·.HasValue .syllabic true))
    (isTransparent := λ _ => false)
    (direction := .rightward)

end Hungarian.VowelHarmony

import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Korean stop nasalization

A Korean stop becomes the nasal of its place before a nasal, so that morpheme-final /p t k/
and /m n ŋ/, which contrast in *pak* 'gourd' and *paŋ* 'room', are pronounced alike before a
nasal: *tɕakɨn-pak nɛmsɛ-ka* 'the smell of a small gourd' and *tɕakɨn-paŋ nɛmsɛ-ka* 'the
smell of a small room' are the same string of sounds, Hayes's illustration of neutralization.
Hayes writes the rule as the change of a non-affricate stop to a voiced nasal sonorant before
a nasal, leaving its place alone, and that is how it is written here over the segments the
rule needs.

## Main definitions

* `Korean.Phonology.stopNasalization` — a non-affricate stop becomes a voiced nasal sonorant
  before a nasal

## Main results

* `Korean.Phonology.pak_paŋ_neutralized` — *pak* and *paŋ* before *n* derive the same string,
  and *pak* alone is unchanged

## References

* [hayes-2009]
-/

open Phonology Subregular.LocalRewrite

namespace Korean.Phonology

/-! ### Segments -/

/-- The features every plain stop shares. -/
private def stop : List (Feature × Bool) :=
  [(.syllabic, false), (.consonantal, true), (.sonorant, false), (.approximant, false),
    (.continuant, false), (.voice, false), (.delayedRelease, false)]

/-- The features every nasal shares; a nasal is a non-continuant without delayed release, so
the rule's change leaves a nasal as it is. -/
private def nasalSpecs : List (Feature × Bool) :=
  [(.syllabic, false), (.consonantal, true), (.sonorant, true), (.approximant, false),
    (.nasal, true), (.voice, true), (.continuant, false), (.delayedRelease, false)]

/-- The features every vowel shares. -/
private def vowel : List (Feature × Bool) :=
  [(.syllabic, true), (.consonantal, false), (.sonorant, true), (.continuant, true),
    (.voice, true)]

/-- The voiceless bilabial stop. -/
def p : Segment := Segment.ofSpecs (stop ++ [(.labial, true)])

/-- The voiceless alveolar stop. -/
def t : Segment := Segment.ofSpecs (stop ++ [(.coronal, true), (.anterior, true)])

/-- The voiceless velar stop. -/
def k : Segment := Segment.ofSpecs (stop ++ [(.dorsal, true)])

/-- The bilabial nasal. -/
def m : Segment := Segment.ofSpecs (nasalSpecs ++ [(.labial, true)])

/-- The alveolar nasal. -/
def n : Segment := Segment.ofSpecs (nasalSpecs ++ [(.coronal, true), (.anterior, true)])

/-- The velar nasal. -/
def ŋ : Segment := Segment.ofSpecs (nasalSpecs ++ [(.dorsal, true)])

/-- The low vowel. -/
def a : Segment := Segment.ofSpecs vowel

/-- The high front unrounded vowel. -/
def i : Segment :=
  Segment.ofSpecs
    (vowel ++ [(.dorsal, true), (.high, true), (.low, false), (.back, false), (.round, false)])

/-- The high back rounded vowel. -/
def u : Segment :=
  Segment.ofSpecs
    (vowel ++ [(.dorsal, true), (.high, true), (.low, false), (.back, true), (.round, true)])

/-- The alveolar lateral. -/
def l : Segment :=
  Segment.ofSpecs
    [(.syllabic, false), (.consonantal, true), (.sonorant, true), (.continuant, true),
      (.voice, true), (.coronal, true), (.anterior, true), (.lateral, true)]

/-! ### The rule -/

/-- A non-affricate stop becomes a voiced nasal sonorant before a nasal. -/
def stopNasalization : Rule where
  name := "stop nasalization"
  target := Segment.ofSpecs [(.delayedRelease, false)]
  effect := .changeFeatures (Segment.ofSpecs [(.nasal, true), (.voice, true), (.sonorant, true)])
  rightContext := [.seg (Segment.ofSpecs [(.nasal, true)])]

/-- *pak* 'gourd' and *paŋ* 'room' before *n* derive the same string, with the velar nasal;
*pak* alone is unchanged. -/
theorem pak_paŋ_neutralized :
    derive [stopNasalization] [p, a, k, n] = [p, a, ŋ, n] ∧
      derive [stopNasalization] [p, a, ŋ, n] = [p, a, ŋ, n] ∧
      derive [stopNasalization] [p, a, k] = [p, a, k] := by
  decide

end Korean.Phonology

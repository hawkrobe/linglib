import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Korean stop nasalization

A Korean stop becomes a nasal before a nasal: *pap* 'rice' with *-man* 'only' is *pamman*.
Hayes writes the rule as the change of a non-affricate stop to a voiced nasal sonorant before
a nasal, and that is how it is written here, over the segments the rule needs.

## Main definitions

* `Korean.Phonology.stopNasalization` — the rule

## Main results

* `Korean.Phonology.pap_man` — *pap-man* surfaces with a bilabial nasal in place of the
  second stop, and *pap* alone is unchanged

## References

* [hayes-2009]
-/

open Phonology Subregular.LocalRewrite

namespace Korean.Phonology

/-! ### Segments -/

/-- The features every plain stop shares. -/
private def stop : List (Feature × Bool) :=
  [(.syllabic, false), (.consonantal, true), (.sonorant, false), (.continuant, false),
    (.voice, false), (.delayedRelease, false)]

/-- The features every nasal shares. -/
private def nasalSpecs : List (Feature × Bool) :=
  [(.syllabic, false), (.consonantal, true), (.sonorant, true), (.nasal, true), (.voice, true)]

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

/-- *pap-man* surfaces with a bilabial nasal for its second stop and nothing else changed;
*pap* alone is unchanged. -/
theorem pap_man :
    (∃ s, derive [stopNasalization] [p, a, p, m, a, n] = [p, a, s, m, a, n] ∧ m ≤ s) ∧
      derive [stopNasalization] [p, a, p] = [p, a, p] :=
  ⟨⟨_, rfl, by decide⟩, by decide⟩

end Korean.Phonology

import Linglib.Phonology.Segmental.FeatureClass
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Tagalog nasal substitution

Tagalog has a process by which a prefix-final nasal and a following stem-initial obstruent
coalesce into a nasal at the obstruent's place: *maŋ-* with *bigáj* 'give' gives *mamigáj* 'to
distribute', and /p b/ yield /m/, /t d/ yield /n/ and /k g/ yield /ŋ/. It is written here as
two ordered rules, the assimilation of a nasal to the place of a following obstruent, a process
of its own in Hayes's textbook, and the deletion of an obstruent after a nasal; the
assimilation copies the place class. Whether a given prefix and stem undergo the process is
variable, from nearly always for /p/ to about half the time for /g/ in Zuraw's dictionary
counts, so *paŋ-* with *tabój* 'goad' keeps its cluster in *pantabój*. The rules give the
substituted form; the variation is the matter of the studies of Zuraw, of Zuraw and Hayes and
of Magri.

## Main definitions

* `Tagalog.Phonology.placeAssimilation`, `Tagalog.Phonology.obstruentDeletion`,
  `Tagalog.Phonology.nasalSubstitution` — the two rules and their sequence

## Main results

* `Tagalog.Phonology.mamigaj` — *maŋ-* with *bigáj* derives *mamigáj*, and the bare stem is
  unchanged
* `Tagalog.Phonology.coalescence` — each obstruent coalesces with a preceding nasal into the
  nasal of its place

## References

* [hayes-2009]
* [magri-2025]
* [zuraw-2010]
* [zuraw-hayes-2017]
-/

open Phonology Subregular.LocalRewrite

namespace Tagalog.Phonology

/-! ### Segments -/

/-- The features every stop shares. -/
private def stop : List (Feature × Bool) :=
  [(.syllabic, false), (.consonantal, true), (.sonorant, false), (.continuant, false)]

/-- The features every nasal shares. -/
private def nasalSpecs : List (Feature × Bool) :=
  [(.syllabic, false), (.consonantal, true), (.sonorant, true), (.nasal, true), (.voice, true)]

/-- The voiceless bilabial stop. -/
def p : Segment := Segment.ofSpecs (stop ++ [(.voice, false), (.labial, true)])

/-- The voiceless alveolar stop. -/
def t : Segment :=
  Segment.ofSpecs (stop ++ [(.voice, false), (.coronal, true), (.anterior, true)])

/-- The voiceless velar stop. -/
def k : Segment := Segment.ofSpecs (stop ++ [(.voice, false), (.dorsal, true)])

/-- The voiced bilabial stop. -/
def b : Segment := Segment.ofSpecs (stop ++ [(.voice, true), (.labial, true)])

/-- The voiced alveolar stop. -/
def d : Segment :=
  Segment.ofSpecs (stop ++ [(.voice, true), (.coronal, true), (.anterior, true)])

/-- The voiced velar stop. -/
def g : Segment := Segment.ofSpecs (stop ++ [(.voice, true), (.dorsal, true)])

/-- The bilabial nasal. -/
def m : Segment := Segment.ofSpecs (nasalSpecs ++ [(.labial, true)])

/-- The alveolar nasal. -/
def n : Segment := Segment.ofSpecs (nasalSpecs ++ [(.coronal, true), (.anterior, true)])

/-- The velar nasal. -/
def ŋ : Segment := Segment.ofSpecs (nasalSpecs ++ [(.dorsal, true)])

/-- The low vowel. -/
def a : Segment :=
  Segment.ofSpecs
    [(.syllabic, true), (.consonantal, false), (.sonorant, true), (.continuant, true),
      (.voice, true), (.low, true)]

/-- The high front vowel. -/
def i : Segment :=
  Segment.ofSpecs
    [(.syllabic, true), (.consonantal, false), (.sonorant, true), (.continuant, true),
      (.voice, true), (.high, true)]

/-- The palatal glide. -/
def j : Segment :=
  Segment.ofSpecs
    [(.syllabic, false), (.consonantal, false), (.sonorant, true), (.continuant, true),
      (.voice, true), (.high, true)]

/-! ### The rules -/

/-- A nasal takes the place of a following obstruent. -/
def placeAssimilation : Rule where
  name := "nasal place assimilation"
  target := Segment.ofSpecs [(.nasal, true)]
  effect := .copyRight FeatureClass.place
  rightContext := [.seg (Segment.ofSpecs [(.consonantal, true), (.sonorant, false)])]

/-- An obstruent deletes after a nasal. -/
def obstruentDeletion : Rule where
  name := "post-nasal obstruent deletion"
  target := Segment.ofSpecs [(.consonantal, true), (.sonorant, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(.nasal, true)])]

/-- Nasal substitution: place assimilation feeding obstruent deletion. -/
def nasalSubstitution : List Rule := [placeAssimilation, obstruentDeletion]

/-- *maŋ-* with *bigáj* derives *mamigáj*; the bare stem is unchanged. -/
theorem mamigaj :
    derive nasalSubstitution [m, a, ŋ, b, i, g, a, j] = [m, a, m, i, g, a, j] ∧
      derive nasalSubstitution [b, i, g, a, j] = [b, i, g, a, j] := by
  decide

/-- Each obstruent coalesces with a preceding nasal into the nasal of its place. -/
theorem coalescence :
    derive nasalSubstitution [ŋ, p] = [m] ∧ derive nasalSubstitution [ŋ, b] = [m] ∧
      derive nasalSubstitution [ŋ, t] = [n] ∧ derive nasalSubstitution [ŋ, d] = [n] ∧
      derive nasalSubstitution [ŋ, k] = [ŋ] ∧ derive nasalSubstitution [ŋ, g] = [ŋ] := by
  decide

end Tagalog.Phonology

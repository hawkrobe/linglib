import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Latin phonemes

This file lists the phonemes of Classical Latin and gives each its segment. Cser's synchronic
phonology of the language is the source for the inventory: five vowel qualities, six oral
stops, the voiceless fricatives /f s/, the nasals /m n/, the liquids /l r/ and the
labio-velar glide written ⟨v⟩. The feature values of a phoneme are not listed here. Each
phoneme names its glyph in the PHOIBLE chart, and its segment is the segment of that chart
entry, so the values are PHOIBLE's.

## Main definitions

* `Latin.Phoneme`: the phonemes.
* `Latin.Phoneme.chart`: the PHOIBLE chart entry of a phoneme.
* `Latin.Phoneme.segment`: the segment of a phoneme.

## Main results

* `Latin.Phoneme.segment_injective`: distinct phonemes are distinct segments.
* `Latin.Phoneme.isVowel_iff`, `Latin.Phoneme.ofSegment_eq_nasal_iff`,
  `Latin.Phoneme.ofSegment_eq_liquid_iff`, `Latin.Phoneme.ofSegment_eq_glide_iff`: the
  vowels and the sonorant consonants fall in their sonority classes.

## Implementation notes

Vowel length is prosodic. Hayes treats duration as a property of the syllable, the feature
system has no [long], and a long vowel is two morae, so only the five qualities are phonemes
here. Clear and dark /l/ are positional variants of the one /l/, which the chart leaves
unspecified for [back], as Sen's analysis of the variants requires. Orthographic ⟨v⟩ is the
glide [w], [−consonantal], which is what lets Belth's tier projection of *pluv-* skip it.

## TODO

* The labio-velars /kʷ/ and /gʷ/, which the chart omits as contour-valued, the rare /h/ and
  /y/, and the diphthongs.

## References

* [cser-2020]
* [sen-2015]
* [belth-2026]
* [hayes-2009]
* [moran-mccloy-2019]
-/

open Phonology Data.PHOIBLE

namespace Latin

/-- The phonemes of Classical Latin. The constructor `w` is orthographic ⟨v⟩. -/
inductive Phoneme where
  | a | e | i | o | u
  | p | b | t | d | k | g
  | f | s
  | m | n
  | l | r
  | w
  deriving DecidableEq, Fintype, Repr

namespace Phoneme

/-- The PHOIBLE chart entry of a phoneme. The voiced velar stop is the IPA glyph `ɡ`, and
/r/ is the alveolar trill. -/
def chart : Phoneme → FeatureMatrix
  | a => .«a» | e => .«e» | i => .«i» | o => .«o» | u => .«u»
  | p => .«p» | b => .«b» | t => .«t» | d => .«d» | k => .«k» | g => .«ɡ»
  | f => .«f» | s => .«s»
  | m => .«m» | n => .«n»
  | l => .«l» | r => .«r»
  | w => .«w»

/-- The segment of a phoneme is the segment of its chart entry. -/
def segment (x : Phoneme) : Segment := x.chart.toSegment

theorem segment_injective : Function.Injective segment := by decide

theorem isVowel_iff (x : Phoneme) :
    x.segment.IsVowel ↔ x ∈ ({a, e, i, o, u} : Finset Phoneme) := by
  revert x; decide

theorem ofSegment_eq_nasal_iff (x : Phoneme) :
    Sonority.ofSegment x.segment = .nasal ↔ x = m ∨ x = n := by
  revert x; decide

theorem ofSegment_eq_liquid_iff (x : Phoneme) :
    Sonority.ofSegment x.segment = .liquid ↔ x = l ∨ x = r := by
  revert x; decide

theorem ofSegment_eq_glide_iff (x : Phoneme) : Sonority.ofSegment x.segment = .glide ↔ x = w := by
  revert x; decide

end Phoneme

end Latin

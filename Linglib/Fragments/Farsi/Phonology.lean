import Linglib.Data.PHOIBLE.Inventories.Persian
import Linglib.Phonology.Segmental.SegmentLike

/-!
# Persian phonemes

This file lists the Persian phonemes that the hiatus data use and gives each its segment.
Modern Persian distinguishes six vowels, front unrounded /i e æ/ against back /u o ɑ/, the
back series rounded except for the variably rounded low vowel, and some two dozen consonants,
among them the glottal stop /ʔ/ that breaks vowel hiatus. The vowels are here with /h tʃ m n ʔ/.
The feature values of a phoneme are not listed. Each phoneme names its glyph in the PHOIBLE
chart, and its segment is the segment of that chart entry.

## Main definitions

* `Farsi.Phoneme`: the phonemes, with `chart`, read as segments.
* `Farsi.e`, `Farsi.h` and the like: the segment of each phoneme, under its symbol.

## Main results

* `Farsi.Phoneme.chart_mem_pes`: each phoneme is in PHOIBLE's Persian inventory.
* `Farsi.Phoneme.isVowel_iff`: the six vowels are the vowels.

## Implementation notes

PHOIBLE's Persian inventory is the Stanford Phonology Archive's, which writes the low front
vowel `a̟` and the affricate `t̠ʃ`, and those are the chart entries taken here. Majidi and
Ternes transcribe the vowel /æ/.

## References

* [majidi-ternes-1991]
* [moran-mccloy-2019]
* [hayes-2009]
* [ariyaee-jurgec-2021]
-/

open Phonology Data.PHOIBLE

namespace Farsi

/-- The Persian phonemes of the hiatus data. A constructor is the phoneme's IPA symbol where
that is an identifier, and otherwise the symbol's name: `scriptA` is ɑ, `tesh` is tʃ and
`glottalStop` is ʔ. -/
inductive Phoneme where
  | i | e | æ | u | o | scriptA
  | h | tesh | m | n | glottalStop
  deriving DecidableEq, Fintype, Repr

namespace Phoneme

/-- The PHOIBLE chart entry of a phoneme, in the glyphs of the Persian inventory. -/
def chart : Phoneme → FeatureMatrix
  | i => .«i» | e => .«e» | æ => .«a̟» | u => .«u» | o => .«o» | scriptA => .«ɑ»
  | h => .«h» | tesh => .«t̠ʃ» | m => .«m» | n => .«n» | glottalStop => .«ʔ»

end Phoneme

/-- A phoneme is read as the segment of its chart entry. -/
instance : SegmentLike Phoneme where
  coe x := .ofChart x.chart
  coe_injective' := by decide

segment_constants Phoneme

namespace Phoneme

/-- Each phoneme is in PHOIBLE's Persian inventory. -/
theorem chart_mem_pes (x : Phoneme) :
    x.chart ∈ Inventories.Persian.pes.phonemes.map (·.features) := by
  cases x <;> decide

theorem isVowel_iff (x : Phoneme) :
    (x : Segment).IsVowel ↔ x ∈ ({i, e, æ, u, o, scriptA} : Finset Phoneme) := by
  revert x; decide

end Phoneme

end Farsi

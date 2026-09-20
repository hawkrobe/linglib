import Linglib.Phonology.Segmental.SegmentLike
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# English phonemes

This file lists the English phonemes that Hayes's textbook examples use and gives each its
segment, together with two of the book's English rules as local rewrite rules. The feature
values of a phoneme are not listed here. Each phoneme names its glyph in the PHOIBLE chart,
and its segment is the segment of that chart entry, so the values are PHOIBLE's.

## Main definitions

* `English.Phoneme`: the phonemes, with `chart`, read as segments.
* `English.p`, `English.esh` and the like: the segment of each phoneme, under its symbol.
* `English.preglottalization`, `English.postnasalDeletion`: two rules of Hayes's.

## Implementation notes

The transcription is Hayes's, with plain /p t k/. PHOIBLE's English inventories write the
voiceless stops aspirated, so no inventory contains these glyphs, and membership in one is not
stated. English /ɹ/ is the chart's `ɹ`, which is [−consonantal] and so a glide in sonority.

## References

* [hayes-2009]
* [moran-mccloy-2019]
-/

open Phonology Subregular.LocalRewrite Data.PHOIBLE

namespace English

/-- The English phonemes of the examples. A constructor is the phoneme's IPA symbol where that
is an identifier, and otherwise the symbol's name: `dezh` is dʒ, `esh` is ʃ, `turnedR` is ɹ,
`smallCapitalI` is ɪ, `wedge` is ʌ and `schwa` is ə. -/
inductive Phoneme where
  | p | t | k | b | d | g | dezh
  | m | n | ŋ
  | f | v | s | θ | esh
  | l | w | turnedR
  | æ | smallCapitalI | i | wedge | o | schwa
  deriving DecidableEq, Fintype, Repr

namespace Phoneme

/-- The PHOIBLE chart entry of a phoneme. The voiced velar stop is the IPA glyph `ɡ`. -/
def chart : Phoneme → FeatureMatrix
  | p => .«p» | t => .«t» | k => .«k» | b => .«b» | d => .«d» | g => .«ɡ» | dezh => .«d̠ʒ»
  | m => .«m» | n => .«n» | ŋ => .«ŋ»
  | f => .«f» | v => .«v» | s => .«s» | θ => .«θ» | esh => .«ʃ»
  | l => .«l» | w => .«w» | turnedR => .«ɹ»
  | æ => .«æ» | smallCapitalI => .«ɪ» | i => .«i» | wedge => .«ʌ» | o => .«o» | schwa => .«ə»

end Phoneme

/-- A phoneme is read as the segment of its chart entry. -/
instance : SegmentLike Phoneme where
  coe x := .ofChart x.chart
  coe_injective' := by decide

segment_constants Phoneme

/-! ### Rules -/

/-- Preglottalization glottalizes a voiceless stop word-finally,
`[−cont, −voice] → [+c.g.] / __ ]word`. -/
def preglottalization : Rule where
  name := "Preglottalization"
  target := Segment.ofSpecs
    [(Phonology.Feature.continuant, false), (Phonology.Feature.voice, false)]
  effect := .changeFeatures (Segment.ofSpecs [(Phonology.Feature.constrGlottis, true)])
  rightContext := [.wordBoundary]

/-- Postnasal /t/ deletion removes a voiceless coronal stop between a nasal and a vowel,
`[−cont, +cor, +ant, −voice] → ∅ / [+nasal] __ [+syll]`. -/
def postnasalDeletion : Rule where
  name := "Postnasal /t/ Deletion"
  target := Segment.ofSpecs
    [(Phonology.Feature.continuant, false), (Phonology.Feature.coronal, true),
     (Phonology.Feature.anterior, true), (Phonology.Feature.voice, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(Phonology.Feature.nasal, true)])]
  rightContext := [.seg (Segment.ofSpecs [(Phonology.Feature.syllabic, true)])]

end English

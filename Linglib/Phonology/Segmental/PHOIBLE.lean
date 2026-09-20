import Linglib.Data.PHOIBLE.Chart
import Linglib.Phonology.Segmental.Basic

/-!
# Segments from PHOIBLE feature matrices

This file turns a PHOIBLE feature matrix into a `Segment`, so that a fragment can take the
feature values of its phonemes from the PHOIBLE chart instead of listing them. PHOIBLE's
features extend those of Hayes, which `Phonology.Feature` follows, with length, tone, stress
and further laryngeal and tongue-root features. Each of Hayes's features is a PHOIBLE column,
under another name for [voice], [constricted glottis] and [ATR], and the segment of a matrix
reads the matrix along that correspondence, dropping the columns Hayes lacks.

The two systems differ in one convention. PHOIBLE specifies [round] only on labial segments
and marks it not applicable elsewhere, where Hayes's charts give every other segment
[−round]. The segment of a matrix therefore takes [−round] as its default.

## Main definitions

* `Phonology.Feature.toPHOIBLE`: the PHOIBLE column of each feature.
* `Data.PHOIBLE.FeatureMatrix.toSegment`: the segment of a feature matrix.

## Main results

* `Phonology.Feature.toPHOIBLE_injective`: distinct features are distinct columns.
* `Data.PHOIBLE.FeatureMatrix.toSegment_apply_of_ne_round`: off [round], a segment has the
  values of its matrix.

## Implementation notes

Dropping PHOIBLE's further features can identify two phonemes of an inventory, a long and a
short vowel or a plain and a fortis stop. A fragment guards against this by proving its map
from phonemes to segments injective. Velar consonants are [−front, −back] in PHOIBLE, so a
vowel tier is picked out by `Segment.IsVowel` and not by the absence of a [back] value.

## References

* [moran-mccloy-2019]
* [hayes-2009]
-/

namespace Phonology.Feature

/-- The PHOIBLE column of a feature. -/
def toPHOIBLE : Feature → Data.PHOIBLE.Feature
  | .syllabic => .syllabic
  | .consonantal => .consonantal
  | .sonorant => .sonorant
  | .approximant => .approximant
  | .continuant => .continuant
  | .delayedRelease => .delayedRelease
  | .nasal => .nasal
  | .lateral => .lateral
  | .strident => .strident
  | .tap => .tap
  | .trill => .trill
  | .voice => .periodicGlottalSource
  | .spreadGlottis => .spreadGlottis
  | .constrGlottis => .constrictedGlottis
  | .labial => .labial
  | .round => .round
  | .labiodental => .labiodental
  | .coronal => .coronal
  | .anterior => .anterior
  | .distributed => .distributed
  | .dorsal => .dorsal
  | .high => .high
  | .low => .low
  | .front => .front
  | .back => .back
  | .tense => .tense
  | .atr => .advancedTongueRoot

theorem toPHOIBLE_injective : Function.Injective toPHOIBLE := by decide

end Phonology.Feature

namespace Data.PHOIBLE.FeatureMatrix

open Phonology

/-- The segment of a feature matrix has the matrix's value for each of Hayes's features, and
[−round] where PHOIBLE marks [round] not applicable. -/
def toSegment (m : FeatureMatrix) : Segment :=
  Bundle.merge (Bundle.comap Feature.toPHOIBLE m) (Segment.ofSpecs [(.round, false)])

theorem toSegment_apply_of_ne_round (m : FeatureMatrix) {f : Phonology.Feature}
    (h : f ≠ .round) : m.toSegment f = m f.toPHOIBLE :=
  Bundle.merge_apply_of_right_eq_none _ (by cases f <;> first | rfl | exact absurd rfl h)

/-- Every segment of a matrix is specified for [round]. -/
theorem toSegment_round_ne_bot (m : FeatureMatrix) : m.toSegment .round ≠ ⊥ := by
  unfold toSegment Bundle.merge
  split
  · exact Option.some_ne_none _
  · exact Option.some_ne_none false

/-! ### Witnesses from the chart -/

/-- Chart segments fall into the sonority classes of their glyphs, the nasal by its
[−approximant]. -/
example : [«p», «s», «n», «l», «j», «a»].map (Sonority.ofSegment ∘ toSegment) =
    [.stop, .fricative, .nasal, .liquid, .glide, .vowel] := by decide

/-- An unrounded vowel is [−round] and a rounded one keeps its [+round]. -/
example : «i».toSegment.HasValue .round false ∧ «u».toSegment.HasValue .round true := by decide

/-- A velar stop is [−back], so the absence of a [back] value does not pick out
consonants. -/
example : «k».toSegment.HasValue .back false := by decide

end Data.PHOIBLE.FeatureMatrix

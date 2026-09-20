import Linglib.Data.PHOIBLE.Inventories.Korean
import Linglib.Phonology.Segmental.PHOIBLE
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Korean stop nasalization

A Korean stop becomes the nasal of its place before a nasal, so that morpheme-final /p t k/
and /m n ŋ/, which contrast in *pak* 'gourd' and *paŋ* 'room', are pronounced alike before a
nasal: *tɕakɨn-pak nɛmsɛ-ka* 'the smell of a small gourd' and *tɕakɨn-paŋ nɛmsɛ-ka* 'the
smell of a small room' are the same string of sounds, Hayes's illustration of neutralization.
Hayes writes the rule as the change of a non-affricate stop to a voiced nasal sonorant before
a nasal, leaving its place alone, and that is how it is written here.

The phonemes are the ones the rule needs, and each takes its feature values from its glyph in
the PHOIBLE chart. There a stop and the nasal of its place differ in the three features the
rule writes and in [delayed release], which is minus on a stop and not applicable on a nasal.
The rule's output is therefore the nasal on every feature but [delayed release], and no two
phonemes differ in that feature alone.

## Main definitions

* `Korean.Phoneme`: the phonemes of the illustration, with `chart` and `segment`.
* `Korean.stopNasalization`: a non-affricate stop becomes a voiced nasal sonorant before a
  nasal.

## Main results

* `Korean.Phoneme.segment_injective`, `Korean.Phoneme.chart_mem_kor`: distinct phonemes are
  distinct segments, and each is a phoneme of PHOIBLE's Korean inventory.
* `Korean.pak_paŋ_neutralized`: *pak* and *paŋ* before *n* derive the same string, the one
  with the velar nasal on every feature but [delayed release]; *pak* alone is unchanged.
* `Korean.derive_pak_ne_paŋ`: the derived string is not literally the one with the velar
  nasal, since the rule leaves [−delayed release] in place.
* `Korean.isDistinctive_compl_delayedRelease`: the features other than [delayed release]
  distinguish the phonemes.

## References

* [hayes-2009]
* [moran-mccloy-2019]
-/

open Phonology Subregular.LocalRewrite Data.PHOIBLE

namespace Korean

/-- The phonemes of Hayes's illustration are the plain stops, the nasals, three vowels and the
lateral. -/
inductive Phoneme where
  | p | t | k
  | m | n | ŋ
  | a | i | u
  | l
  deriving DecidableEq, Fintype, Repr

namespace Phoneme

/-- The PHOIBLE chart entry of a phoneme. -/
def chart : Phoneme → FeatureMatrix
  | p => .«p» | t => .«t» | k => .«k»
  | m => .«m» | n => .«n» | ŋ => .«ŋ»
  | a => .«a» | i => .«i» | u => .«u»
  | l => .«l»

/-- The segment of a phoneme is the segment of its chart entry. -/
def segment (x : Phoneme) : Segment := x.chart.toSegment

theorem segment_injective : Function.Injective segment := by decide

/-- Each phoneme is in PHOIBLE's Korean inventory. -/
theorem chart_mem_kor (x : Phoneme) :
    x.chart ∈ Inventories.Korean.kor.phonemes.map (·.features) := by
  cases x <;> decide

end Phoneme

/-- The segments of the illustration. -/
def inventory : Finset Segment := Finset.univ.image Phoneme.segment

/-! ### The rule -/

/-- A non-affricate stop becomes a voiced nasal sonorant before a nasal. -/
def stopNasalization : Rule where
  name := "stop nasalization"
  target := Segment.ofSpecs [(.delayedRelease, false)]
  effect := .changeFeatures (Segment.ofSpecs [(.nasal, true), (.voice, true), (.sonorant, true)])
  rightContext := [.seg (Segment.ofSpecs [(.nasal, true)])]

/-- The features other than [delayed release]. -/
def exceptDelayedRelease : Finset Phonology.Feature := {.delayedRelease}ᶜ

/-- No two phonemes differ in [delayed release] alone. -/
theorem isDistinctive_compl_delayedRelease : IsDistinctive exceptDelayedRelease inventory := by
  decide

/-- *pak* 'gourd' and *paŋ* 'room' before *n* derive the same string, which has the velar
nasal on every feature but [delayed release]; *paŋ* is unchanged there, and so is *pak*
alone. -/
theorem pak_paŋ_neutralized :
    (derive [stopNasalization] ([.p, .a, .k, .n].map Phoneme.segment)).map
        (Bundle.restrict exceptDelayedRelease) =
      ([.p, .a, .ŋ, .n].map Phoneme.segment).map (Bundle.restrict exceptDelayedRelease) ∧
      derive [stopNasalization] ([.p, .a, .ŋ, .n].map Phoneme.segment) =
        [.p, .a, .ŋ, .n].map Phoneme.segment ∧
      derive [stopNasalization] ([.p, .a, .k].map Phoneme.segment) =
        [.p, .a, .k].map Phoneme.segment := by
  decide

/-- The string derived from *pak* before *n* is not the string with the velar nasal itself,
because the rule leaves the stop its [−delayed release]. -/
theorem derive_pak_ne_paŋ :
    derive [stopNasalization] ([.p, .a, .k, .n].map Phoneme.segment) ≠
      [.p, .a, .ŋ, .n].map Phoneme.segment := by
  decide

end Korean

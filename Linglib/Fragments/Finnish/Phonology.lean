import Linglib.Data.PHOIBLE.Inventories.Finnish
import Linglib.Phonology.Segmental.PHOIBLE
import Linglib.Phonology.Harmony.System

/-!
# Finnish phonology

This file gives the Finnish vowels as segments and states palatal harmony over them. In
Karlsson's description the vowels fall into three classes. The back vowels /ɑ o u/ and the
front vowels /æ ø y/, written ⟨a o u⟩ and ⟨ä ö y⟩, do not mix within a word, and the neutral
vowels /e i/ occur with either set. A suffix vowel alternates with the stem, so that the
partitive is *kirja-a* 'book' but *käsi-ä* 'hand', and the inessive *talo-ssa* 'in the house'
but *metsä-ssä* 'in the forest'. Harmony is a single system in the sense of Rose and Walker.
The feature [back] spreads rightward from the last harmonic stem vowel to suffix vowels
unspecified for it, consonants and the neutral vowels are transparent, and a stem with no
harmonic vowel takes front suffixes.

The feature values come from the PHOIBLE chart, read at the vowels of a PHOIBLE Finnish
inventory and kept on the features that distinguish the eight vowels. The alternating suffix
vowel is the meet of /ɑ/ and /æ/, the features they share, and so has no value for [back].

## Main definitions

* `Finnish.Vowel`, `Finnish.Consonant`: the vowels, and the
  consonants of the example forms, each with `chart` and `segment`.
* `Finnish.archiphonemeA`: the alternating suffix vowel.
* `Finnish.palatalHarmony`: palatal harmony.

## Main results

* `Finnish.Vowel.segment_injective`, `Finnish.Vowel.chart_mem_fin`:
  the contrastive features distinguish the vowels, and each is a phoneme of the inventory.
* `Finnish.Vowel.isNeutral_iff`: the neutral vowels are /e i/ and the back
  vowels /ɑ o u/.
* `Finnish.archiphonemeA_unspecified_back`, `Finnish.setFeature_back_archiphonemeA`: the
  suffix vowel has no [back], and with [back] filled in it is /ɑ/ or /æ/.
* `Finnish.sourceValue_back`: a back stem vowel is the source across a neutral
  one, and a stem of neutral vowels has no source.

## Implementation notes

The inventory is PHOIBLE 2535, which transcribes the low back vowel [ɑ] and the mid vowels
with lowering diacritics. The consonants take plain chart glyphs, which that inventory
writes with place diacritics, so membership is stated for the vowels only.

## References

* [karlsson-2017]
* [rose-walker-2011]
* [goldsmith-1976]
* [moran-mccloy-2019]
-/

namespace Finnish

open Phonology Phonology.Harmony Data.PHOIBLE

/-! ### Vowels -/

/-- The features that distinguish the vowels, with [syllabic] marking them as vowels. -/
def contrastive : Finset Phonology.Feature := {.syllabic, .high, .low, .back, .round}

/-- The eight vowels. A constructor is the vowel's IPA symbol where that is an identifier,
and `scriptA` is ɑ; `scriptA`, `æ` and `ø` are orthographic ⟨a⟩, ⟨ä⟩ and ⟨ö⟩. -/
inductive Vowel where
  | scriptA | o | u
  | æ | ø | y
  | e | i
  deriving DecidableEq, Fintype, Repr

namespace Vowel

/-- The PHOIBLE chart entry of a vowel, in the glyphs of the inventory. -/
def chart : Vowel → FeatureMatrix
  | scriptA => .«ɑ» | o => .«o̞» | u => .«u»
  | æ => .«æ» | ø => .«ø̞» | y => .«y»
  | e => .«e̞» | i => .«i»

/-- The segment of a vowel is its chart entry's on the contrastive features. -/
def segment (v : Vowel) : Segment := Bundle.restrict contrastive v.chart.toSegment

theorem segment_injective : Function.Injective segment := by decide

/-- Each vowel is in PHOIBLE's Finnish inventory. -/
theorem chart_mem_fin (v : Vowel) :
    v.chart ∈ Inventories.Finnish.fin.phonemes.map (·.features) := by
  cases v <;> decide

end Vowel

/-- The archiphoneme /A/, the vowel of the alternating suffixes such as the essive -nA and the
partitive -A, is what /ɑ/ and /æ/ share. -/
def archiphonemeA : Segment := Vowel.scriptA.segment ⊓ Vowel.æ.segment

/-! ### Consonants -/

/-- The consonants of the example forms. -/
inductive Consonant where
  | p | t | k | n | v | l | j
  deriving DecidableEq, Fintype, Repr

namespace Consonant

/-- The PHOIBLE chart entry of a consonant. -/
def chart : Consonant → FeatureMatrix
  | p => .«p» | t => .«t» | k => .«k» | n => .«n» | v => .«v» | l => .«l» | j => .«j»

/-- The segment of a consonant is the segment of its chart entry. -/
def segment (c : Consonant) : Segment := c.chart.toSegment

theorem segment_injective : Function.Injective segment := by decide

end Consonant

/-! ### Harmonic classification -/

/-- A back vowel is [+syllabic, +back]. -/
def IsBackVowel (s : Segment) : Prop := s.HasValue .syllabic true ∧ s.HasValue .back true

/-- A neutral vowel is front, unrounded and non-low, and is transparent to harmony. -/
def IsNeutral (s : Segment) : Prop :=
  s.HasValue .syllabic true ∧ s.HasValue .back false ∧ s.HasValue .round false ∧
    s.HasValue .low false

instance : DecidablePred IsBackVowel := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsNeutral := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The neutral vowels are /e i/ and the back vowels /ɑ o u/. -/
theorem Vowel.isNeutral_iff (v : Vowel) :
    (IsNeutral v.segment ↔ v = .e ∨ v = .i) ∧
      (IsBackVowel v.segment ↔ v = .scriptA ∨ v = .o ∨ v = .u) := by
  revert v; decide

/-! ### The harmony system -/

/-- Finnish palatal harmony spreads [back] from the last harmonic stem vowel to the suffix
vowels unspecified for it, and a stem with no harmonic vowel takes front suffixes by default.
Consonants and the neutral vowels /e i/ are off the tier. -/
def palatalHarmony : System Segment :=
  System.mk' (feature := .back)
    (IsTarget := fun s ↦ s.HasValue .syllabic true ∧ s .back = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true ∨ IsNeutral s)
    (direction := .rightward)
    (default := some false)

/-- The suffix vowel has no value for [back], so it is a target of harmony. -/
theorem archiphonemeA_unspecified_back : archiphonemeA.Unspecified .back := by decide

/-- The suffix vowel with [back] filled in is /ɑ/ or /æ/. -/
theorem setFeature_back_archiphonemeA :
    archiphonemeA.setFeature .back true = Vowel.scriptA.segment ∧
      archiphonemeA.setFeature .back false = Vowel.æ.segment := by
  decide

/-- A back stem vowel is the source of harmony, also across a following neutral vowel. A front
harmonic vowel is the source of front harmony, and a stem of neutral vowels has no source,
so that it takes the default. -/
theorem sourceValue_back :
    palatalHarmony.searchCopy.sourceValue [Vowel.scriptA.segment] = some true ∧
      palatalHarmony.searchCopy.sourceValue [Vowel.scriptA.segment, Vowel.i.segment] =
        some true ∧
      palatalHarmony.searchCopy.sourceValue [Vowel.æ.segment] = some false ∧
      palatalHarmony.searchCopy.sourceValue [Vowel.e.segment, Vowel.i.segment] = none := by
  decide

end Finnish

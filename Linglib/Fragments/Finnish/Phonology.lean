import Linglib.Data.PHOIBLE.Inventories.Finnish
import Linglib.Phonology.Segmental.SegmentLike
import Linglib.Phonology.Harmony.System
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Finnish phonology

This file gives Finnish phonemes as segments and states palatal harmony and consonant
gradation over them. In Karlsson's description the vowels fall into three classes. The back
vowels /ɑ o u/ and the front vowels /æ ø y/, written ⟨a o u⟩ and ⟨ä ö y⟩, do not mix within a
word, and the neutral vowels /e i/ occur with either set. A suffix vowel alternates with the stem, so that the
partitive is *kirja-a* 'book' but *käsi-ä* 'hand', and the inessive *talo-ssa* 'in the house'
but *metsä-ssä* 'in the forest'. Harmony is a single system in the sense of Rose and Walker.
The feature [back] spreads rightward from the last harmonic stem vowel to suffix vowels
unspecified for it, consonants and the neutral vowels are transparent, and a stem with no
harmonic vowel takes front suffixes.

The feature values come from the PHOIBLE chart, read at the vowels of a PHOIBLE Finnish
inventory and kept on the features that distinguish the eight vowels. The alternating suffix
vowel is the meet of /ɑ/ and /æ/, the features they share, and so has no value for [back].
Phonemes are named by their letters, so a list of them reads as the word is spelled.

Consonant gradation, the second of Karlsson's two important sound alternations, weakens a
stop at the onset of a syllable that an ending closes. The long stops shorten, *kukka*
'flower' but *kuka-n*, which is quantitative gradation, and the short stops change, *katu*
'street' but *kadu-lla*, *tupa* 'hut' but *tuva-ssa*, *tauko* 'pause' but *tauo-n*, which is
qualitative gradation. By Karlsson's rule A the ending consists of one consonant or begins
with two, and only a short vowel stands between the stop and the ending, so that *katto*
'roof' gives *kato-n* and *kato-lla* but *katto-na*.

## Main definitions

* `Finnish.Phoneme`: the vowels and the consonants of the example forms, with `chart` and
  `contrastive`, read as segments.
* `Finnish.a`, `Finnish.k` and the like: the segment of each phoneme, under its letter.
* `Finnish.A`: the alternating suffix vowel.
* `Finnish.palatalHarmony`: palatal harmony.
* `Finnish.ofChar`: the phoneme that a letter writes.
* `Finnish.consonantGradation`: the qualitative rules followed by the quantitative ones.

## Main results

* `Finnish.Phoneme.chart_mem_fin`: each vowel is a phoneme of PHOIBLE's Finnish inventory.
* `Finnish.isNeutral_iff`, `Finnish.isBackVowel_iff`: the neutral vowels are /e i/ and the
  back vowels /ɑ o u/.
* `Finnish.unspecified_back_A`, `Finnish.setFeature_back_A`: the suffix vowel has no [back],
  and with [back] filled in it is /ɑ/ or /æ/.
* `Finnish.sourceValue_back`: a back stem vowel is the source across a neutral one, and a
  stem of neutral vowels has no source.
* `Finnish.katto`: Karlsson's paradigm of *katto*, gradation in *katon*, *katolla* and
  *katolta* and none in *kattona*.
* `Finnish.quantitative_gradation`, `Finnish.qualitative_gradation`: his examples of the two
  types.

## Implementation notes

The inventory is PHOIBLE 2535, which transcribes the low back vowel [ɑ] and the mid vowels
with lowering diacritics. The consonants take plain chart glyphs, which that inventory
writes with place diacritics, so membership is stated for the vowels only.

A rule has one right context, so each alternation is two rules, one for an ending of a
single consonant and one for an ending that begins with two. The qualitative rules apply
first, since the short stop that quantitative gradation leaves does not weaken again. The
qualitative rules are stated after a vowel. A long stop is two segments, and so is a long
vowel, which the rules do not yet tell from a short one.

## TODO

* The qualitative alternations after /h l r/ and the assimilations after a nasal or liquid,
  Karlsson's types (6) and (8) to (12), the rare types (13) to (16), the ban on gradation
  before a long vowel, and rule B for verbs.

## References

* [karlsson-2017]
* [rose-walker-2011]
* [goldsmith-1976]
* [moran-mccloy-2019]
-/

namespace Finnish

open Phonology Phonology.Harmony Subregular.LocalRewrite Data.PHOIBLE

/-! ### Segments -/

/-- The phonemes, named by their letters, where `a` is ɑ, `ä` is æ and `ö` is ø. The
consonants are those of the example forms. -/
inductive Phoneme where
  | a | o | u | ä | ö | y | e | i
  | p | t | k | d | s | n | v | l | j
  deriving DecidableEq, Fintype, Repr

namespace Phoneme

/-- The PHOIBLE chart entry of a phoneme, the vowels in the glyphs of the inventory. -/
def chart : Phoneme → FeatureMatrix
  | a => .«ɑ» | o => .«o̞» | u => .«u» | ä => .«æ» | ö => .«ø̞» | y => .«y» | e => .«e̞»
  | i => .«i» | p => .«p» | t => .«t» | k => .«k» | d => .«d» | s => .«s» | n => .«n»
  | v => .«v» | l => .«l» | j => .«j»

/-- The vowels. -/
def vowels : Finset Phoneme := {a, o, u, ä, ö, y, e, i}

/-- A vowel keeps the features that distinguish the eight vowels, with [syllabic] marking it
as a vowel, and a consonant keeps every feature. -/
def contrastive (x : Phoneme) : Finset Phonology.Feature :=
  if x ∈ vowels then {.syllabic, .high, .low, .back, .round} else Finset.univ

/-- Each vowel is in PHOIBLE's Finnish inventory. -/
theorem chart_mem_fin (x : Phoneme) (hx : x ∈ vowels) :
    x.chart ∈ Inventories.Finnish.fin.phonemes.map (·.features) := by
  revert x; decide

end Phoneme

/-- A phoneme is read as its chart entry's segment on its contrastive features. -/
instance : SegmentLike Phoneme where
  coe x := .ofChart x.chart ⊥ x.contrastive
  coe_injective' := by decide

segment_constants Phoneme

/-- `A` is the vowel of the alternating suffixes such as the essive -nA and the partitive -A.
It is what `a` and `ä` share. -/
def A : Segment := a ⊓ ä

/-! ### Harmonic classification -/

/-- A back vowel is [+syllabic, +back]. -/
def IsBackVowel (s : Segment) : Prop := s.HasValue .syllabic true ∧ s.HasValue .back true

/-- A neutral vowel is front, unrounded and non-low, and is transparent to harmony. -/
def IsNeutral (s : Segment) : Prop :=
  s.HasValue .syllabic true ∧ s.HasValue .back false ∧ s.HasValue .round false ∧
    s.HasValue .low false

instance : DecidablePred IsBackVowel := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsNeutral := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The neutral vowels are /e i/. -/
theorem isNeutral_iff (x : Phoneme) : IsNeutral x ↔ x = .e ∨ x = .i := by revert x; decide

/-- The back vowels are /ɑ o u/. -/
theorem isBackVowel_iff (x : Phoneme) : IsBackVowel x ↔ x = .a ∨ x = .o ∨ x = .u := by
  revert x; decide

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
theorem unspecified_back_A : A.Unspecified .back := by decide

/-- The suffix vowel with [back] filled in is /ɑ/ or /æ/. -/
theorem setFeature_back_A : A.setFeature .back true = a ∧ A.setFeature .back false = ä := by
  decide

/-- A back stem vowel is the source of harmony, also across a following neutral vowel. A front
harmonic vowel is the source of front harmony, and a stem of neutral vowels has no source,
so that it takes the default. -/
theorem sourceValue_back :
    palatalHarmony.searchCopy.sourceValue [a] = some true ∧
      palatalHarmony.searchCopy.sourceValue [a, i] = some true ∧
      palatalHarmony.searchCopy.sourceValue [ä] = some false ∧
      palatalHarmony.searchCopy.sourceValue [e, i] = none := by
  decide

/-! ### Spelling -/

/-- `ofChar c` is the phoneme that the letter `c` writes. A long vowel or stop is written
double. -/
def ofChar : Char → Option Phoneme
  | 'a' => some .a | 'o' => some .o | 'u' => some .u | 'ä' => some .ä | 'ö' => some .ö
  | 'y' => some .y | 'e' => some .e | 'i' => some .i | 'p' => some .p | 't' => some .t
  | 'k' => some .k | 'd' => some .d | 's' => some .s | 'n' => some .n | 'v' => some .v
  | 'l' => some .l | 'j' => some .j
  | _ => none

/-! ### Consonant gradation -/

/-- A vowel, as a rule context. -/
private def vowel : ContextElem := .seg (Segment.ofSpecs [(.syllabic, true)])

/-- A consonant, as a rule context. -/
private def consonant : ContextElem := .seg (Segment.ofSpecs [(.syllabic, false)])

/-- The rules weakening `target` after `left`, before a short vowel and an ending that is one
consonant or begins with two. -/
def gradation (target : Segment) (effect : Effect) (left : ContextElem) : List Rule :=
  [[vowel, consonant, .wordBoundary], [vowel, consonant, consonant]].map fun right ↦
    { target, effect, leftContext := [left], rightContext := right }

/-- In qualitative gradation after a vowel, /p/ becomes /v/, /t/ becomes /d/ and /k/ is
lost. -/
def qualitativeGradation : List Rule :=
  gradation p (.replace v) vowel ++
    gradation t (.changeFeatures (Segment.ofSpecs [(.voice, true)])) vowel ++
    gradation k .delete vowel

/-- In quantitative gradation a long stop loses its second half. -/
def quantitativeGradation : List Rule :=
  [p, t, k].flatMap fun c ↦ gradation c .delete (.seg c)

/-- Consonant gradation is the qualitative rules followed by the quantitative ones. -/
def consonantGradation : List Rule := qualitativeGradation ++ quantitativeGradation

/-- Karlsson's paradigm of *katto* 'roof'. The genitive, adessive and ablative endings close
the syllable and the long stop shortens, and before the essive -na it does not. -/
theorem katto :
    derive consonantGradation [k, a, t, t, o, n] = [k, a, t, o, n] ∧
      derive consonantGradation [k, a, t, t, o, l, l, a] = [k, a, t, o, l, l, a] ∧
      derive consonantGradation [k, a, t, t, o, l, t, a] = [k, a, t, o, l, t, a] ∧
      derive consonantGradation [k, a, t, t, o, n, a] = [k, a, t, t, o, n, a] := by
  decide

/-- Quantitative gradation in *kaappi* 'cupboard' and *kukka* 'flower'. -/
theorem quantitative_gradation :
    derive consonantGradation [k, a, a, p, p, i, s, s, a] = [k, a, a, p, i, s, s, a] ∧
      derive consonantGradation [k, u, k, k, a, n] = [k, u, k, a, n] := by
  decide

/-- Qualitative gradation in *tupa* 'hut', *katu* 'street' and *tauko* 'pause'. -/
theorem qualitative_gradation :
    derive consonantGradation [t, u, p, a, s, s, a] = [t, u, v, a, s, s, a] ∧
      derive consonantGradation [k, a, t, u, l, l, a] = [k, a, d, u, l, l, a] ∧
      derive consonantGradation [t, a, u, k, o, n] = [t, a, u, o, n] := by
  decide

end Finnish

import Linglib.Data.PHOIBLE.Inventories.Finnish
import Linglib.Phonology.Segmental.PHOIBLE
import Linglib.Phonology.Harmony.System
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Finnish phonology

This file gives Finnish vowels and consonants as segments and states palatal harmony and
consonant gradation over them. In
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

Consonant gradation, the second of Karlsson's two important sound alternations, weakens a
stop at the onset of a syllable that an ending closes. The long stops shorten, *kukka*
'flower' but *kuka-n*, which is quantitative gradation, and the short stops change, *katu*
'street' but *kadu-lla*, *tupa* 'hut' but *tuva-ssa*, *tauko* 'pause' but *tauo-n*, which is
qualitative gradation. By Karlsson's rule A the ending consists of one consonant or begins
with two, and only a short vowel stands between the stop and the ending, so that *katto*
'roof' gives *kato-n* and *kato-lla* but *katto-na*.

## Main definitions

* `Finnish.Vowel`, `Finnish.Consonant`: the vowels, and the
  consonants of the example forms, each with `chart` and `segment`.
* `Finnish.archiphonemeA`: the alternating suffix vowel.
* `Finnish.palatalHarmony`: palatal harmony.
* `Finnish.ofChar`, `Finnish.segments`: the segment a letter writes, and the segments of a
  written form.
* `Finnish.consonantGradation`: the qualitative rules followed by the quantitative ones.

## Main results

* `Finnish.Vowel.segment_injective`, `Finnish.Vowel.chart_mem_fin`:
  the contrastive features distinguish the vowels, and each is a phoneme of the inventory.
* `Finnish.Vowel.isNeutral_iff`: the neutral vowels are /e i/ and the back
  vowels /ɑ o u/.
* `Finnish.archiphonemeA_unspecified_back`, `Finnish.setFeature_back_archiphonemeA`: the
  suffix vowel has no [back], and with [back] filled in it is /ɑ/ or /æ/.
* `Finnish.sourceValue_back`: a back stem vowel is the source across a neutral
  one, and a stem of neutral vowels has no source.

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
  | p | t | k | d | s | n | v | l | j
  deriving DecidableEq, Fintype, Repr

namespace Consonant

/-- The PHOIBLE chart entry of a consonant. -/
def chart : Consonant → FeatureMatrix
  | p => .«p» | t => .«t» | k => .«k» | d => .«d» | s => .«s»
  | n => .«n» | v => .«v» | l => .«l» | j => .«j»

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

/-! ### Written forms -/

/-- The segment a letter of Finnish orthography writes, with `A` for the archiphoneme. -/
def ofChar : Char → Option Segment
  | 'a' => some Vowel.scriptA.segment | 'ä' => some Vowel.æ.segment
  | 'o' => some Vowel.o.segment | 'ö' => some Vowel.ø.segment
  | 'u' => some Vowel.u.segment | 'y' => some Vowel.y.segment
  | 'e' => some Vowel.e.segment | 'i' => some Vowel.i.segment
  | 'p' => some Consonant.p.segment | 't' => some Consonant.t.segment
  | 'k' => some Consonant.k.segment | 'd' => some Consonant.d.segment
  | 's' => some Consonant.s.segment | 'n' => some Consonant.n.segment
  | 'v' => some Consonant.v.segment | 'l' => some Consonant.l.segment
  | 'j' => some Consonant.j.segment | 'A' => some archiphonemeA
  | _ => none

/-- The segments of a written form. A long vowel or stop, written double, is two segments. -/
def segments (form : String) : List Segment := form.toList.filterMap ofChar

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
  gradation Consonant.p.segment (.replace Consonant.v.segment) vowel ++
    gradation Consonant.t.segment (.changeFeatures (Segment.ofSpecs [(.voice, true)])) vowel ++
    gradation Consonant.k.segment .delete vowel

/-- In quantitative gradation a long stop loses its second half. -/
def quantitativeGradation : List Rule :=
  [Consonant.p, .t, .k].flatMap fun c ↦ gradation c.segment .delete (.seg c.segment)

/-- Consonant gradation is the qualitative rules followed by the quantitative ones. -/
def consonantGradation : List Rule := qualitativeGradation ++ quantitativeGradation

/-- The written forms of the theorems below. -/
private def forms : List String :=
  ["katton", "katon", "kattolla", "katolla", "kattolta", "katolta", "kattona", "kaappissa",
    "kaapissa", "kukkan", "kukan", "tupassa", "tuvassa", "katulla", "kadulla", "taukon",
    "tauon"]

/-- Every letter of the written forms is read. -/
theorem length_segments : ∀ w ∈ forms, (segments w).length = w.length := by decide

/-- Karlsson's paradigm of *katto* 'roof'. The genitive, adessive and ablative endings close
the syllable and the long stop shortens, and before the essive -na it does not. -/
theorem katto :
    derive consonantGradation (segments "katton") = segments "katon" ∧
      derive consonantGradation (segments "kattolla") = segments "katolla" ∧
      derive consonantGradation (segments "kattolta") = segments "katolta" ∧
      derive consonantGradation (segments "kattona") = segments "kattona" := by
  decide

/-- Quantitative gradation in *kaappi* 'cupboard' and *kukka* 'flower'. -/
theorem quantitative_gradation :
    derive consonantGradation (segments "kaappissa") = segments "kaapissa" ∧
      derive consonantGradation (segments "kukkan") = segments "kukan" := by
  decide

/-- Qualitative gradation in *tupa* 'hut', *katu* 'street' and *tauko* 'pause'. -/
theorem qualitative_gradation :
    derive consonantGradation (segments "tupassa") = segments "tuvassa" ∧
      derive consonantGradation (segments "katulla") = segments "kadulla" ∧
      derive consonantGradation (segments "taukon") = segments "tauon" := by
  decide

end Finnish

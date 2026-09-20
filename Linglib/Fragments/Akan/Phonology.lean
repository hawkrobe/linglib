import Linglib.Data.PHOIBLE.Inventories.Akan
import Linglib.Phonology.Segmental.SegmentLike
import Linglib.Phonology.Segmental.FeatureClass

/-!
# Akan segments

This file lists the vowels of Akan as segments, together with the two consonants of its
velar–palatal alternation. Akan has nine vowels, /i ɪ e ɛ a ɔ o ʊ u/, which Dolphyne
groups into an advanced set /i e o u/ and an unadvanced set /ɪ ɛ a ɔ ʊ/ that do not mix
within a word, the tongue-root harmony Stewart identified; in Casali's typology the
inventory is a five-height system, with the low vowel the only one lacking a partner. In
Akuapem and Asante a tenth quality, the advanced variant of /a/ before syllables with
/i u/, joins the advanced set; it is not represented here. Velar stops become corono-dorsal
palatal affricates before front vowels, the alternation McCarthy and Prince's account of
Akan reduplication turns on.

The feature values come from the PHOIBLE chart. The chart codes the two vowel sets by
[tense] and marks every plain vowel [−ATR], where the Akan literature has [ATR] carry the
contrast, so a vowel departs from the chart by taking the chart's [tense] value as its [ATR]
value, and [tense] is not contrastive. The chart omits the palatal affricate, whose values
are contours, and its segment is the velar stop's with the features McCarthy and Prince's
corono-dorsal analysis adds.

## Main definitions

* `Akan.Vowel`: the nine vowels, with `chart` and `departure`, read as segments.
* `Akan.Vowel.atr`: the [ATR] value of each vowel.
* `Akan.Consonant`: the velar stop and its palatalized output, read as segments.
* `Akan.i`, `Akan.k` and the like: each vowel and consonant as a segment, under its symbol.

## Main results

* `Akan.Vowel.chart_mem_aka`: each vowel is a phoneme of PHOIBLE's Akan inventory.
* `Akan.Vowel.coe_apply`: a vowel has the chart's values off [ATR] and [tense].
* `Akan.Vowel.atr_iff`: the advanced vowels are /i e o u/.
* `Akan.Consonant.restrict_tcCurl_eq_k`: the affricate has the stop's values off the four features
  palatalization writes.

## References

* [dolphyne-1988]
* [stewart-1967]
* [casali-2003]
* [mccarthy-prince-1995]
* [hayes-2009]
* [moran-mccloy-2019]
-/

open Phonology Data.PHOIBLE

namespace Akan

/-! ### Vowels -/

/-- The nine vowels of Akan. A constructor is the vowel's IPA symbol where that is an
identifier, and otherwise the symbol's name: `smallCapitalI` is ɪ, `epsilon` is ɛ, `openO`
is ɔ and `upsilon` is ʊ. -/
inductive Vowel where
  | i | e | o | u
  | smallCapitalI | epsilon | a | openO | upsilon
  deriving DecidableEq, Repr, Fintype

namespace Vowel

/-- The PHOIBLE chart entry of a vowel. -/
def chart : Vowel → FeatureMatrix
  | i => .«i» | e => .«e» | o => .«o» | u => .«u»
  | smallCapitalI => .«ɪ» | epsilon => .«ɛ» | a => .«a» | openO => .«ɔ» | upsilon => .«ʊ»

/-- A vowel departs from its chart entry by taking the chart's [tense] value as its [ATR]
value. The low vowel, which the chart leaves without [tense], keeps the chart's [−ATR]. -/
def departure (v : Vowel) : Segment := fun f ↦ if f = .atr then v.chart.toSegment .tense else ⊥

/-- Every feature but [tense] is contrastive. -/
def contrastive : Finset Phonology.Feature := {.tense}ᶜ

/-- Each vowel is in PHOIBLE's Akan inventory. -/
theorem chart_mem_aka (v : Vowel) :
    v.chart ∈ Inventories.Akan.aka.phonemes.map (·.features) := by
  cases v <;> decide

end Vowel

/-- A vowel is read as its chart entry's segment, with its departure, on the contrastive
features. -/
instance : SegmentLike Vowel where
  coe v := .ofChart v.chart v.departure Vowel.contrastive
  coe_injective' := by decide

segment_constants Vowel

namespace Vowel

/-- A vowel has the chart's values off [ATR] and [tense]. -/
theorem coe_apply (v : Vowel) {f : Phonology.Feature} (ha : f ≠ .atr) (ht : f ≠ .tense) :
    (v : Segment) f = v.chart.toSegment f :=
  Segment.ofChart_apply (by simpa [contrastive] using ht) (ite_eq_right ha)

/-- The [ATR] value of a vowel is read off its segment. -/
def atr (v : Vowel) : Bool := decide ((v : Segment).HasValue .atr true)

/-- Dolphyne's advanced set is /i e o u/. -/
theorem atr_iff (v : Vowel) : v.atr = true ↔ v ∈ ({i, e, o, u} : Finset Vowel) := by
  revert v; decide

end Vowel

/-! ### The velar–palatal alternation -/

/-- The voiceless velar stop /k/ and the voiceless palatal affricate /tɕ/ it becomes before
a front vowel, `tcCurl` being the name of the symbol tɕ. -/
inductive Consonant where
  | k | tcCurl
  deriving DecidableEq, Repr, Fintype

namespace Consonant

/-- The features palatalization writes on the velar stop. -/
def palatalized : Segment :=
  Segment.ofSpecs [(.coronal, true), (.anterior, false), (.distributed, true),
    (.delayedRelease, true)]

end Consonant

/-- The stop is the chart's /k/. The affricate keeps the stop's values, [+dorsal] among them,
and adds [+coronal, −anterior, +distributed] with delayed release, so it is a corono-dorsal
complex segment. -/
instance : SegmentLike Consonant where
  coe
    | .k => .ofChart .«k»
    | .tcCurl => .ofChart .«k» Consonant.palatalized
  coe_injective' := by decide

segment_constants Consonant

namespace Consonant

/-- The affricate has the stop's values off the features palatalization writes. -/
theorem restrict_tcCurl_eq_k :
    Bundle.restrict ({.coronal, .anterior, .distributed, .delayedRelease}ᶜ) (tcCurl : Segment) =
      Bundle.restrict ({.coronal, .anterior, .distributed, .delayedRelease}ᶜ) (k : Segment) := by
  decide

end Consonant

/-- Palatalization changes the value of [coronal]. -/
theorem k_tcCurl_coronal :
    k.HasValue .coronal false ∧
      tcCurl.HasValue .coronal true := by
  decide

/-- The palatal affricate has two designated articulators. -/
theorem tcCurl_isComplex : tcCurl.IsComplex := by decide

/-- The front vowel /ɪ/ triggers palatalization and the low vowel /a/ does not. -/
theorem smallCapitalI_front_a_not_front :
    smallCapitalI.HasValue .front true ∧
      a.HasValue .front false := by
  decide

end Akan

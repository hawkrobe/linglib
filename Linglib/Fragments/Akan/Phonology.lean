import Linglib.Data.PHOIBLE.Inventories.Akan
import Linglib.Phonology.Segmental.PHOIBLE
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
contrast, so a vowel's segment reads the chart's [tense] value as its [ATR] value and has no
[tense]. The chart omits the palatal affricate, whose values are contours, and its segment is
the velar stop's with the features McCarthy and Prince's corono-dorsal analysis adds.

## Main definitions

* `Akan.Vowel`: the nine vowels, with `chart` and `segment`.
* `Akan.Vowel.atr`: the [ATR] value of each vowel.
* `Akan.inventory`: the set of vowel segments.
* `Akan.Consonant`: the velar stop and its palatalized output, with `segment`.

## Main results

* `Akan.Vowel.segment_injective`, `Akan.Vowel.chart_mem_aka`: distinct vowels are distinct
  segments, and each is a phoneme of PHOIBLE's Akan inventory.
* `Akan.Vowel.restrict_segment_eq_chart`: a vowel's segment has the chart's values off [ATR] and
  [tense].
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

/-- The features on which a vowel's segment departs from its chart entry. -/
def recoded : Finset Phonology.Feature := {.atr, .tense}

/-- The segment of a vowel has the chart's [tense] value as its [ATR] value, no [tense], and
the chart's values elsewhere. The low vowel, which the chart leaves without [tense], keeps
the chart's [−ATR]. -/
def segment (v : Vowel) : Segment :=
  Bundle.merge (fun f ↦ if f = .atr then v.chart.toSegment .tense else ⊥)
    (Bundle.restrict {.tense}ᶜ v.chart.toSegment)

theorem segment_injective : Function.Injective segment := by decide

/-- Each vowel is in PHOIBLE's Akan inventory. -/
theorem chart_mem_aka (v : Vowel) :
    v.chart ∈ Inventories.Akan.aka.phonemes.map (·.features) := by
  cases v <;> decide

/-- A vowel's segment has the chart's values off [ATR] and [tense]. -/
theorem restrict_segment_eq_chart (v : Vowel) :
    Bundle.restrict recodedᶜ v.segment = Bundle.restrict recodedᶜ v.chart.toSegment := by
  cases v <;> decide

/-- The [ATR] value of a vowel is read off its segment. -/
def atr (v : Vowel) : Bool := decide (v.segment.HasValue .atr true)

/-- Dolphyne's advanced set is /i e o u/. -/
theorem atr_iff (v : Vowel) : v.atr = true ↔ v ∈ ({i, e, o, u} : Finset Vowel) := by
  revert v; decide

end Vowel

/-- The set of vowel segments. -/
def inventory : Finset Segment := Finset.univ.image Vowel.segment

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

/-- The segment of each consonant. The stop is the chart's /k/. The affricate keeps the stop's
values, [+dorsal] among them, and adds [+coronal, −anterior, +distributed] with delayed
release, so it is a corono-dorsal complex segment. -/
def segment : Consonant → Segment
  | k => FeatureMatrix.«k».toSegment
  | tcCurl => Bundle.merge palatalized FeatureMatrix.«k».toSegment

/-- The affricate has the stop's values off the features palatalization writes. -/
theorem restrict_tcCurl_eq_k :
    Bundle.restrict ({.coronal, .anterior, .distributed, .delayedRelease}ᶜ) tcCurl.segment =
      Bundle.restrict ({.coronal, .anterior, .distributed, .delayedRelease}ᶜ) k.segment := by
  decide

end Consonant

/-- Palatalization changes the value of [coronal]. -/
theorem k_tcCurl_coronal :
    Consonant.k.segment.HasValue .coronal false ∧
      Consonant.tcCurl.segment.HasValue .coronal true := by
  decide

/-- The palatal affricate has two designated articulators. -/
theorem tcCurl_isComplex : Consonant.tcCurl.segment.IsComplex := by decide

/-- The front vowel /ɪ/ triggers palatalization and the low vowel /a/ does not. -/
theorem smallCapitalI_front_a_not_front :
    Vowel.smallCapitalI.segment.HasValue .front true ∧
      Vowel.a.segment.HasValue .front false := by
  decide

end Akan

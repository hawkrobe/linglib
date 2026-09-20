import Linglib.Data.PHOIBLE.Inventories.Tagalog
import Linglib.Phonology.Segmental.SegmentLike
import Linglib.Phonology.Segmental.FeatureClass
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Tagalog nasal substitution

Tagalog has a process by which a prefix-final nasal and a following stem-initial obstruent
coalesce into a nasal at the obstruent's place: *maŋ-* with *bigáj* 'give' gives *mamigáj* 'to
distribute', and /p b/ yield /m/, /t d/ yield /n/ and /k g/ yield /ŋ/. It is written here as
two ordered rules, the assimilation of a nasal to the place of a following obstruent, a process
of its own in Hayes's textbook, and the deletion of an obstruent after a nasal; the
assimilation copies the place class. Whether a given prefix and stem undergo the process is
variable, from nearly always for /p/ to about half the time for /g/ in Zuraw's dictionary
counts, so *paŋ-* with *tabój* 'goad' keeps its cluster in *pantabój*. The rules give the
substituted form; the variation is the matter of the studies of Zuraw, of Zuraw and Hayes and
of Magri.

The phonemes are the ones the examples need, and each takes its feature values from its glyph
in the PHOIBLE chart. There the nasal of a place has exactly the place features of the stops
of that place, so copying the place class onto /ŋ/ gives the chart's own /m/, /n/ or /ŋ/.

## Main definitions

* `Tagalog.Phoneme`: the phonemes of the examples, with `chart`, read as segments.
* `Tagalog.placeAssimilation`, `Tagalog.obstruentDeletion`, `Tagalog.nasalSubstitution`: the
  two rules and their sequence.

## Main results

* `Tagalog.Phoneme.chart_mem_tgl`: each phoneme is in PHOIBLE's Tagalog inventory.
* `Tagalog.mamigaj`: *maŋ-* with *bigáj* derives *mamigáj*, and the bare stem is unchanged.
* `Tagalog.coalescence`: each stop coalesces with a preceding nasal into the nasal of its
  place.

## References

* [hayes-2009]
* [magri-2025]
* [zuraw-2010]
* [zuraw-hayes-2017]
* [moran-mccloy-2019]
-/

open Phonology Subregular.LocalRewrite Data.PHOIBLE

namespace Tagalog

/-- The phonemes of the examples are the six oral stops, the nasals of their places, two
vowels and the palatal glide. -/
inductive Phoneme where
  | p | t | k
  | b | d | g
  | m | n | ŋ
  | a | i
  | j
  deriving DecidableEq, Fintype, Repr

namespace Phoneme

/-- The PHOIBLE chart entry of a phoneme. The voiced velar stop is the IPA glyph `ɡ`. -/
def chart : Phoneme → FeatureMatrix
  | p => .«p» | t => .«t» | k => .«k»
  | b => .«b» | d => .«d» | g => .«ɡ»
  | m => .«m» | n => .«n» | ŋ => .«ŋ»
  | a => .«a» | i => .«i»
  | j => .«j»

/-- A phoneme is read as the segment of its chart entry. -/
instance : SegmentLike Phoneme where
  coe x := .ofChart x.chart
  coe_injective' := by decide

/-- Each phoneme is in PHOIBLE's Tagalog inventory. -/
theorem chart_mem_tgl (x : Phoneme) :
    x.chart ∈ Inventories.Tagalog.tgl.phonemes.map (·.features) := by
  cases x <;> decide

end Phoneme

/-! ### The rules -/

/-- A nasal takes the place of a following obstruent. -/
def placeAssimilation : Rule where
  name := "nasal place assimilation"
  target := Segment.ofSpecs [(.nasal, true)]
  effect := .copyRight FeatureClass.place
  rightContext := [.seg (Segment.ofSpecs [(.consonantal, true), (.sonorant, false)])]

/-- An obstruent deletes after a nasal. -/
def obstruentDeletion : Rule where
  name := "post-nasal obstruent deletion"
  target := Segment.ofSpecs [(.consonantal, true), (.sonorant, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(.nasal, true)])]

/-- Nasal substitution is place assimilation feeding obstruent deletion. -/
def nasalSubstitution : List Rule := [placeAssimilation, obstruentDeletion]

/-- *maŋ-* with *bigáj* derives *mamigáj*; the bare stem is unchanged. -/
theorem mamigaj :
    derive nasalSubstitution (([.m, .a, .ŋ, .b, .i, .g, .a, .j] : List Phoneme)) =
        ([.m, .a, .m, .i, .g, .a, .j] : List Phoneme) ∧
      derive nasalSubstitution (([.b, .i, .g, .a, .j] : List Phoneme)) =
        ([.b, .i, .g, .a, .j] : List Phoneme) := by
  decide

/-- The nasal at the place of a stop or nasal. A vowel or glide is left as it is. -/
def Phoneme.nasal : Phoneme → Phoneme
  | .p | .b => .m
  | .t | .d => .n
  | .k | .g => .ŋ
  | x => x

/-- Each stop coalesces with a preceding nasal into the nasal of its place. -/
theorem coalescence (x : Phoneme) (hx : x ∈ ({.p, .b, .t, .d, .k, .g} : Finset Phoneme)) :
    derive nasalSubstitution (([.ŋ, x] : List Phoneme)) = ([x.nasal] : List Phoneme) := by
  revert x; decide

end Tagalog

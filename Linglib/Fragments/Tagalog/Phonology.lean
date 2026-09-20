import Linglib.Data.PHOIBLE.Inventories.Tagalog
import Linglib.Phonology.Segmental.PHOIBLE
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

* `Tagalog.Phoneme`: the phonemes of the examples, with `chart` and `segment`.
* `Tagalog.placeAssimilation`, `Tagalog.obstruentDeletion`, `Tagalog.nasalSubstitution`: the
  two rules and their sequence.

## Main results

* `Tagalog.Phoneme.segment_injective`, `Tagalog.Phoneme.chart_mem_tgl`: distinct phonemes are
  distinct segments, and each is a phoneme of PHOIBLE's Tagalog inventory.
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

/-- The segment of a phoneme is the segment of its chart entry. -/
def segment (x : Phoneme) : Segment := x.chart.toSegment

theorem segment_injective : Function.Injective segment := by decide

/-- Each phoneme is in PHOIBLE's Tagalog inventory. -/
theorem chart_mem_tgl (x : Phoneme) :
    x.chart ∈ Inventories.Tagalog.tgl.phonemes.map (·.features) := by
  cases x <;> decide

end Phoneme

/-- The segments of a string of phonemes. -/
def segments (l : List Phoneme) : List Segment := l.map Phoneme.segment

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
    derive nasalSubstitution (segments [.m, .a, .ŋ, .b, .i, .g, .a, .j]) =
        segments [.m, .a, .m, .i, .g, .a, .j] ∧
      derive nasalSubstitution (segments [.b, .i, .g, .a, .j]) =
        segments [.b, .i, .g, .a, .j] := by
  decide

/-- The nasal at the place of a stop or nasal. A vowel or glide is left as it is. -/
def Phoneme.nasal : Phoneme → Phoneme
  | .p | .b => .m
  | .t | .d => .n
  | .k | .g => .ŋ
  | x => x

/-- Each stop coalesces with a preceding nasal into the nasal of its place. -/
theorem coalescence (x : Phoneme) (hx : x ∈ ({.p, .b, .t, .d, .k, .g} : Finset Phoneme)) :
    derive nasalSubstitution (segments [.ŋ, x]) = segments [x.nasal] := by
  revert x; decide

end Tagalog

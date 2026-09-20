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

* `Tagalog.a`, `Tagalog.p` and the like: the phonemes of the examples, as segments of their
  chart entries.
* `Tagalog.inventory`: the set of them.
* `Tagalog.placeAssimilation`, `Tagalog.obstruentDeletion`, `Tagalog.nasalSubstitution`: the
  two rules and their sequence.

## Main results

* `Tagalog.exists_mem_tgl`: each phoneme is the segment of one in PHOIBLE's Tagalog
  inventory.
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

/-! ### Phonemes -/

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The voiced alveolar stop /d/. -/
def d : Segment := .ofChart .«d»

/-- The voiced velar stop /g/, the IPA glyph `ɡ` in the chart. -/
def g : Segment := .ofChart .«ɡ»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The velar nasal /ŋ/. -/
def ŋ : Segment := .ofChart .«ŋ»

/-- The low vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The palatal glide /j/. -/
def j : Segment := .ofChart .«j»

/-- The phonemes of the examples are the six oral stops, the nasals of their places, two
vowels and the palatal glide, and they are pairwise distinct. -/
def inventory : Finset Segment := ⟨↑[p, t, k, b, d, g, m, n, ŋ, a, i, j], by decide⟩

/-- Each phoneme is the segment of a phoneme of PHOIBLE's Tagalog inventory. -/
theorem exists_mem_tgl :
    ∀ x ∈ inventory, ∃ y ∈ Inventories.Tagalog.tgl.phonemes, x = .ofChart y.features := by
  decide

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
    derive nasalSubstitution [m, a, ŋ, b, i, g, a, j] = [m, a, m, i, g, a, j] ∧
      derive nasalSubstitution [b, i, g, a, j] = [b, i, g, a, j] := by
  decide

/-- Each stop coalesces with a preceding nasal into the nasal of its place. -/
theorem coalescence :
    ∀ x ∈ [(p, m), (b, m), (t, n), (d, n), (k, ŋ), (g, ŋ)],
      derive nasalSubstitution [ŋ, x.1] = [x.2] := by
  decide

end Tagalog

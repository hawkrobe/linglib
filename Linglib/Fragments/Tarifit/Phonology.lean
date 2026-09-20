import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Tarifit phones

This file lists the consonants of Tarifit (Nador variety) that occur in the CCəC target words
of Afkir and Zellou's production study, as they surface in the simple imperative, together with
the schwa, and gives each its segment. Singleton /b, d, t/ spirantize to [β, ð, θ] outside
post-nasal and pharyngealized contexts. The sonority class of a phone on the Parker scale is
read off its segment by `Sonority.Class.ofSegment` and not stored.

The feature values come from the PHOIBLE chart, and the segment of a phone is its chart
entry's with the phone's departure merged over it. There are two departures. PHOIBLE separates
the pharyngealized stops /tˤ dˤ/ from plain /t d/ by its retracted tongue root feature alone,
which the feature system here lacks, so they take the chart entries of /t d/ and the value
[+back]. Afkir and Zellou describe the pharyngeal /ʕ/ as an approximant, where the chart has a
fricative. PHOIBLE has no Tarifit inventory.

## Main definitions

* `Tarifit.Phone`: the phones, with `ipa`, `chart`, `departure` and `segment`.
* `Tarifit.Phone.sonorityClass`, `Tarifit.Phone.rank`, `Tarifit.Phone.Voiceless`: the Parker
  class and rank of a phone, and the voiceless obstruents.

## Main results

* `Tarifit.Phone.segment_injective`: distinct phones are distinct segments.
* `Tarifit.Phone.departure_eq_bot_iff`: the phones that depart from the chart are the two
  pharyngealized stops and the pharyngeal.
* `Tarifit.Phone.restrict_segment_eq_chart`: a phone's segment has the chart's values off the
  four features a departure writes.

## References

* [afkir-zellou-2025]
* [parker-2002]
* [moran-mccloy-2019]
-/

open Phonology Data.PHOIBLE

namespace Tarifit

/-- The phones of the CCəC target words, as they surface. A constructor is the phone's IPA
symbol where that is an identifier, and otherwise the symbol's name; `emphaticT` and
`emphaticD` are the pharyngealized stops tˤ and dˤ, `ghayn` is ʁ, `ayn` is ʕ and `hbar` is
ħ. -/
inductive Phone
  | q | k | t | emphaticT | emphaticD | beta | eth | theta | f | s | esh | chi | hbar | z | ezh
  | ghayn | ayn | m | n | r | l | schwa
  deriving DecidableEq, Fintype, Repr

namespace Phone

/-- The IPA transcription of a phone. -/
def ipa : Phone → String
  | .q => "q" | .k => "k" | .t => "t" | .emphaticT => "tˤ" | .emphaticD => "dˤ" | .beta => "β"
  | .eth => "ð" | .theta => "θ" | .f => "f" | .s => "s" | .esh => "ʃ" | .chi => "χ"
  | .hbar => "ħ" | .z => "z" | .ezh => "ʒ" | .ghayn => "ʁ" | .ayn => "ʕ" | .m => "m"
  | .n => "n" | .r => "r" | .l => "l" | .schwa => "ə"

/-- The PHOIBLE chart entry of a phone. The pharyngealized stops take the entries of the
plain stops, and /r/ is the tap. -/
def chart : Phone → FeatureMatrix
  | .q => .«q» | .k => .«k» | .t => .«t» | .emphaticT => .«t» | .emphaticD => .«d»
  | .beta => .«β» | .eth => .«ð» | .theta => .«θ» | .f => .«f» | .s => .«s» | .esh => .«ʃ»
  | .chi => .«χ» | .hbar => .«ħ» | .z => .«z» | .ezh => .«ʒ» | .ghayn => .«ʁ» | .ayn => .«ʕ»
  | .m => .«m» | .n => .«n» | .r => .«ɾ» | .l => .«l» | .schwa => .«ə»

/-- The values on which a phone departs from its chart entry are [+back] on the pharyngealized
stops and the values of an approximant on the pharyngeal. -/
def departure : Phone → Segment
  | .emphaticT | .emphaticD => Segment.ofSpecs [(.back, true)]
  | .ayn => Segment.ofSpecs [(.consonantal, false), (.sonorant, true), (.approximant, true)]
  | _ => ⊥

/-- The features a departure writes. -/
def departed : Finset Phonology.Feature := {.back, .consonantal, .sonorant, .approximant}

/-- The segment of a phone is its chart entry's with its departure merged over it. -/
def segment (x : Phone) : Segment := Bundle.merge x.departure x.chart.toSegment

theorem segment_injective : Function.Injective segment := by decide

/-- The phones that depart from the chart are the pharyngealized stops and the pharyngeal. -/
theorem departure_eq_bot_iff (x : Phone) :
    x.departure = ⊥ ↔ x ∉ ({.emphaticT, .emphaticD, .ayn} : Finset Phone) := by
  revert x; decide

/-- A phone's segment has the chart's values off the features a departure writes. -/
theorem restrict_segment_eq_chart (x : Phone) :
    Bundle.restrict departedᶜ x.segment = Bundle.restrict departedᶜ x.chart.toSegment := by
  revert x; decide

/-- Parker sonority class, read off the phone's features. -/
def sonorityClass (p : Phone) : Sonority.Class := Sonority.Class.ofSegment p.segment

/-- Parker sonority rank. -/
def rank (p : Phone) : ℕ := p.sonorityClass.parkerRank

/-- A voiceless obstruent. -/
def Voiceless (p : Phone) : Prop := p.sonorityClass.Voiceless

instance : DecidablePred Voiceless := fun p ↦ inferInstanceAs (Decidable p.sonorityClass.Voiceless)

end Phone

end Tarifit

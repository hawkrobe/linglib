import Linglib.Phonology.Segmental.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Tarifit phones

The consonants of Tarifit (Nador variety) that occur in the CCəC target words of the production
study, as they surface in the simple imperative, together with the schwa. Singleton /b, d, t/
spirantize to [β, ð, θ] outside post-nasal and pharyngealized contexts, and the pharyngeal /ʕ/
is an approximant. Each phone is a feature-specified `Segment`, so its sonority class on the
Parker scale is read off by `Sonority.Class.ofSegment` rather than stored. PHOIBLE has no
Tarifit inventory.

## References

* [afkir-zellou-2025], §2.1
* [parker-2002]
-/

namespace Tarifit

open Phonology

/-- The phones of the CCəC target words, as they surface. -/
inductive Phone
  | q | k | t | tE | dE | beta | eth | theta | f | s | esh | chi | hbar | z | ezh | ghayn | ayn
  | m | n | r | l | schwa
  deriving DecidableEq, Fintype, Repr

namespace Phone

/-- IPA transcription. -/
def ipa : Phone → String
  | .q => "q" | .k => "k" | .t => "t" | .tE => "tˤ" | .dE => "dˤ" | .beta => "β" | .eth => "ð"
  | .theta => "θ" | .f => "f" | .s => "s" | .esh => "ʃ" | .chi => "χ" | .hbar => "ħ" | .z => "z"
  | .ezh => "ʒ" | .ghayn => "ʁ" | .ayn => "ʕ" | .m => "m" | .n => "n" | .r => "r" | .l => "l"
  | .schwa => "ə"

/-- A voiceless stop. -/
private def vlStop (place : List (Feature × Bool)) : Segment :=
  Segment.ofSpecs ([(.syllabic, false), (.consonantal, true), (.sonorant, false),
    (.continuant, false), (.voice, false)] ++ place)

/-- A fricative of the given voicing. -/
private def fricative (voiced : Bool) (place : List (Feature × Bool)) : Segment :=
  Segment.ofSpecs ([(.syllabic, false), (.consonantal, true), (.sonorant, false),
    (.continuant, true), (.voice, voiced)] ++ place)

/-- The feature specification of each phone: uvular /q/, velar /k/, alveolar /t/, the
pharyngealized /tˤ, dˤ/, the spirants and fricatives, the pharyngeal approximant /ʕ/, the
nasals, the tap /r/, the lateral /l/, and the schwa. -/
def segment : Phone → Segment
  | .q => vlStop [(.dorsal, true), (.back, true)]
  | .k => vlStop [(.dorsal, true), (.high, true)]
  | .t => vlStop [(.coronal, true), (.anterior, true)]
  | .tE => vlStop [(.coronal, true), (.anterior, true), (.back, true)]
  | .dE => Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.sonorant, false),
      (.continuant, false), (.voice, true), (.coronal, true), (.anterior, true), (.back, true)]
  | .beta => fricative true [(.labial, true)]
  | .eth => fricative true [(.coronal, true), (.anterior, true), (.distributed, true)]
  | .theta => fricative false [(.coronal, true), (.anterior, true), (.distributed, true)]
  | .f => fricative false [(.labial, true), (.labiodental, true)]
  | .s => fricative false [(.coronal, true), (.anterior, true), (.strident, true)]
  | .esh => fricative false [(.coronal, true), (.anterior, false), (.strident, true)]
  | .chi => fricative false [(.dorsal, true), (.back, true)]
  | .hbar => fricative false []
  | .z => fricative true [(.coronal, true), (.anterior, true), (.strident, true)]
  | .ezh => fricative true [(.coronal, true), (.anterior, false), (.strident, true)]
  | .ghayn => fricative true [(.dorsal, true), (.back, true)]
  | .ayn => Segment.ofSpecs [(.syllabic, false), (.consonantal, false), (.sonorant, true),
      (.approximant, true), (.continuant, true), (.voice, true)]
  | .m => Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.sonorant, true),
      (.approximant, false), (.nasal, true), (.voice, true), (.labial, true)]
  | .n => Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.sonorant, true),
      (.approximant, false), (.nasal, true), (.voice, true), (.coronal, true), (.anterior, true)]
  | .r => Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.sonorant, true),
      (.approximant, true), (.continuant, true), (.voice, true), (.coronal, true), (.tap, true)]
  | .l => Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.sonorant, true),
      (.approximant, true), (.continuant, true), (.voice, true), (.coronal, true),
      (.lateral, true)]
  | .schwa => Segment.ofSpecs [(.syllabic, true), (.consonantal, false), (.sonorant, true),
      (.approximant, true), (.continuant, true), (.voice, true)]

/-- Parker sonority class, read off the phone's features. -/
def sonorityClass (p : Phone) : Sonority.Class := Sonority.Class.ofSegment p.segment

/-- Parker sonority rank. -/
def rank (p : Phone) : ℕ := p.sonorityClass.parkerRank

/-- A voiceless obstruent. -/
def Voiceless (p : Phone) : Prop := p.sonorityClass.Voiceless

instance : DecidablePred Voiceless := fun p => inferInstanceAs (Decidable p.sonorityClass.Voiceless)

end Phone

end Tarifit

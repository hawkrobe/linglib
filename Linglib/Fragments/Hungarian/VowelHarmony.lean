import Linglib.Data.PHOIBLE.Inventories.Hungarian
import Linglib.Phonology.Segmental.PHOIBLE
import Linglib.Phonology.Harmony.System

/-!
# Hungarian vowel harmony

The short vowels of Hungarian as segments, their harmonic classification, and the two harmony
systems the suffix alternations follow: palatal harmony, the backness of the last harmonic
stem vowel spreading rightward through the transparent neutral vowels, and rounding harmony,
the rounding of the last stem vowel, which resolves the three-way suffixes. The seven vowels
are the system (7) of [siptar-torkenczy-2000], with long vowels identical in features since
length is prosodic; the harmonic classification is that of their (27), the front unrounded
vowels being neutral; and the two systems compile the [rose-walker-2011] decomposition to the
substrate's `Harmony.System`.

The feature values come from the PHOIBLE chart, read at the short vowels of PHOIBLE's
Hungarian inventory and kept on the features the system (7) uses. The short low vowel is the
chart's rounded [ɒ], and Siptár and Törkenczy class it with the unrounded back vowels, its
rounding being a matter of phonetic implementation, so it departs from the chart in [round].

## Main definitions

* `Hungarian.VowelHarmony.Vowel`: the seven short vowels, with `chart`, `departure` and
  `segment`.
* `Hungarian.VowelHarmony.contrastive`: the features the vowel system uses.
* `Hungarian.VowelHarmony.hungarianPalatalHarmony`,
  `Hungarian.VowelHarmony.hungarianLabialHarmony`: the two harmony systems.

## Main results

* `Hungarian.VowelHarmony.Vowel.segment_injective`,
  `Hungarian.VowelHarmony.Vowel.chart_mem_hun`: the contrastive features distinguish the
  vowels, and each vowel is a phoneme of PHOIBLE's Hungarian inventory.
* `Hungarian.VowelHarmony.Vowel.isNeutral_iff`: the neutral vowels are /i/ and /ɛ/.

## Implementation notes

* Antiharmonic stems, vacillating stems and the height-graded transparency of the neutral
  vowels are not properties of these systems: `Studies/SiptarTorkenczy2000` derives them from
  the book's place-feature analysis.

## References

* [siptar-torkenczy-2000]
* [rose-walker-2011]
* [moran-mccloy-2019]
-/

namespace Hungarian.VowelHarmony

open Phonology Phonology.Harmony Data.PHOIBLE

/-! ### The vowel inventory -/

/-- The features the vowel system (7) uses, with [syllabic] marking the vowels. -/
def contrastive : Finset Phonology.Feature := {.syllabic, .high, .low, .back, .round}

/-- The seven short vowels. A constructor is the vowel's IPA symbol where that is an
identifier, and otherwise the symbol's name: `epsilon` is ɛ, orthographic ⟨e⟩, and
`turnedScriptA` is ɒ, orthographic ⟨a⟩; `y` and `ø` are orthographic ⟨ü⟩ and ⟨ö⟩. -/
inductive Vowel where
  | i | y | u | epsilon | ø | o | turnedScriptA
  deriving DecidableEq, Fintype, Repr

namespace Vowel

/-- The PHOIBLE chart entry of a vowel. -/
def chart : Vowel → FeatureMatrix
  | i => .«i» | y => .«y» | u => .«u» | epsilon => .«ɛ» | ø => .«ø» | o => .«o»
  | turnedScriptA => .«ɒ»

/-- The low vowel departs from the chart in being phonologically unrounded. -/
def departure : Vowel → Segment
  | turnedScriptA => Segment.ofSpecs [(.round, false)]
  | _ => ⊥

/-- The segment of a vowel is its chart entry's, with its departure, on the contrastive
features. -/
def segment (v : Vowel) : Segment :=
  Bundle.restrict contrastive (Bundle.merge v.departure v.chart.toSegment)

theorem segment_injective : Function.Injective segment := by decide

/-- Each vowel is in PHOIBLE's Hungarian inventory. -/
theorem chart_mem_hun (v : Vowel) :
    v.chart ∈ Inventories.Hungarian.hun.phonemes.map (·.features) := by
  cases v <;> decide

/-- The vowel written by an orthographic vowel letter, long and short alike. -/
def ofLetter : String → Option Vowel
  | "i" | "í" => some i
  | "ü" | "ű" => some y
  | "u" | "ú" => some u
  | "e" | "é" => some epsilon
  | "ö" | "ő" => some ø
  | "o" | "ó" => some o
  | "a" | "á" => some turnedScriptA
  | _ => none

end Vowel

/-- The segment written by an orthographic vowel letter. -/
def ofLetter (l : String) : Option Segment := (Vowel.ofLetter l).map Vowel.segment

/-- The vowels of a word written as a list of orthographic segments. -/
def vowelsOf (segments : List String) : List Segment := segments.filterMap ofLetter

/-! ### Harmonic classification -/

/-- A vowel is neutral when it is front and unrounded. -/
def IsNeutral (s : Segment) : Prop :=
  s.HasValue .syllabic true ∧ s.HasValue .back false ∧ s.HasValue .round false

/-- A vowel is front harmonic when it is front and rounded. -/
def IsFrontHarmonic (s : Segment) : Prop :=
  s.HasValue .syllabic true ∧ s.HasValue .back false ∧ s.HasValue .round true

/-- Every back vowel is back harmonic. -/
def IsBackHarmonic (s : Segment) : Prop := s.HasValue .syllabic true ∧ s.HasValue .back true

instance : DecidablePred IsNeutral := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsFrontHarmonic := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsBackHarmonic := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The neutral vowels are /i/ and /ɛ/, the front harmonic ones /y/ and /ø/, and the rest are
back harmonic. -/
theorem Vowel.isNeutral_iff (v : Vowel) :
    (IsNeutral v.segment ↔ v = .i ∨ v = .epsilon) ∧
      (IsFrontHarmonic v.segment ↔ v = .y ∨ v = .ø) ∧
      (IsBackHarmonic v.segment ↔ v = .u ∨ v = .o ∨ v = .turnedScriptA) := by
  revert v; decide

/-! ### The harmony systems -/

/-- Palatal harmony spreads the backness of the last harmonic stem vowel rightward to the
suffix vowels unspecified for it, consonants and the neutral vowels being off the tier. -/
def hungarianPalatalHarmony : System Segment :=
  System.mk' (feature := .back)
    (IsTarget := fun s ↦ s.HasValue .syllabic true ∧ s .back = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true ∨ IsNeutral s)
    (direction := .rightward)

/-- Rounding harmony spreads the rounding of the last stem vowel to the suffix vowels
unspecified for it, with no transparent vowels; it matters only for front stems, since a
back stem takes the back alternant of a three-way suffix. -/
def hungarianLabialHarmony : System Segment :=
  System.mk' (feature := .round)
    (IsTarget := fun s ↦ s.HasValue .syllabic true ∧ s .round = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true)
    (direction := .rightward)

end Hungarian.VowelHarmony

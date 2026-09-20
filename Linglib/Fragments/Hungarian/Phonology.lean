import Linglib.Data.PHOIBLE.Inventories.Hungarian
import Linglib.Phonology.Segmental.PHOIBLE
import Linglib.Phonology.Harmony.System

/-!
# Hungarian phonology

This file gives the short vowels of Hungarian as segments, classifies them for harmony, and
states the two harmony systems the suffix alternations follow. The seven vowels are those of
Siptár and Törkenczy's vowel system, and a long vowel has the features of its short
counterpart, length being prosodic. In their classification the front unrounded vowels are
neutral, the front rounded vowels front harmonic, and the back vowels back harmonic. Palatal
harmony spreads the backness of the last harmonic stem vowel rightward through the transparent
neutral vowels. Rounding harmony spreads the rounding of the last stem vowel, and resolves the
three-way suffixes. Both are systems in the sense of Rose and Walker's decomposition.

The feature values come from the PHOIBLE chart, read at the short vowels of PHOIBLE's
Hungarian inventory and kept on the features the system (7) uses. The short low vowel is the
chart's rounded [ɒ], and Siptár and Törkenczy class it with the unrounded back vowels, its
rounding being a matter of phonetic implementation, so it departs from the chart in [round].

## Main definitions

* `Hungarian.contrastive`: the features the vowel system uses.
* `Hungarian.i`, `Hungarian.epsilon` and the like: the seven short vowels, and
  `Hungarian.vowels` the set of them.
* `Hungarian.ofLetter`: the vowel an orthographic letter writes.
* `Hungarian.palatalHarmony`, `Hungarian.labialHarmony`: the two harmony systems.

## Main results

* `Hungarian.exists_mem_hun`: each vowel's chart entry is in PHOIBLE's Hungarian inventory.
* `Hungarian.isNeutral_iff`, `Hungarian.isFrontHarmonic_iff`, `Hungarian.isBackHarmonic_iff`:
  the neutral vowels are /i/ and /ɛ/, the front harmonic ones /y/ and /ø/, and the rest are
  back harmonic.

## Implementation notes

* Antiharmonic stems, vacillating stems and the height-graded transparency of the neutral
  vowels are not properties of these systems: `Studies/SiptarTorkenczy2000` derives them from
  the book's place-feature analysis.

## References

* [siptar-torkenczy-2000]
* [rose-walker-2011]
* [moran-mccloy-2019]
-/

namespace Hungarian

open Phonology Phonology.Harmony Data.PHOIBLE

/-! ### The vowel inventory -/

/-- The features the vowel system (7) uses, with [syllabic] marking the vowels. -/
def contrastive : Finset Phonology.Feature := {.syllabic, .high, .low, .back, .round}

/-- A vowel is its chart entry's segment, with its departure, on the contrastive features. -/
def vowel (m : FeatureMatrix) (departure : Segment := ⊥) : Segment :=
  .ofChart m departure contrastive

/-- The high front unrounded vowel /i/, orthographic ⟨i⟩. -/
def i : Segment := vowel .«i»

/-- The high front rounded vowel /y/, orthographic ⟨ü⟩. -/
def y : Segment := vowel .«y»

/-- The high back vowel /u/. -/
def u : Segment := vowel .«u»

/-- The front unrounded vowel /ɛ/, orthographic ⟨e⟩. -/
def epsilon : Segment := vowel .«ɛ»

/-- The mid front rounded vowel /ø/, orthographic ⟨ö⟩. -/
def ø : Segment := vowel .«ø»

/-- The mid back vowel /o/. -/
def o : Segment := vowel .«o»

/-- The low back vowel /ɒ/, orthographic ⟨a⟩, which departs from the chart in being phonologically
unrounded. -/
def turnedScriptA : Segment := vowel .«ɒ» (Segment.ofSpecs [(.round, false)])

/-- The seven short vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[i, y, u, epsilon, ø, o, turnedScriptA], by decide⟩

/-- Each vowel but the low one, which departs from the chart, is the segment of a phoneme of
PHOIBLE's Hungarian inventory, and the low vowel's chart entry is in that inventory. -/
theorem exists_mem_hun :
    (∀ x ∈ vowels, x ≠ turnedScriptA →
        ∃ y ∈ Inventories.Hungarian.hun.phonemes, x = vowel y.features) ∧
      FeatureMatrix.«ɒ» ∈ Inventories.Hungarian.hun.phonemes.map (·.features) := by
  decide

/-- The vowel written by an orthographic vowel letter, long and short alike. -/
def ofLetter : String → Option Segment
  | "i" | "í" => some i
  | "ü" | "ű" => some y
  | "u" | "ú" => some u
  | "e" | "é" => some epsilon
  | "ö" | "ő" => some ø
  | "o" | "ó" => some o
  | "a" | "á" => some turnedScriptA
  | _ => none

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

/-- The neutral vowels are /i/ and /ɛ/. -/
theorem isNeutral_iff : ∀ x ∈ vowels, IsNeutral x ↔ x = i ∨ x = epsilon := by decide

/-- The front harmonic vowels are /y/ and /ø/. -/
theorem isFrontHarmonic_iff : ∀ x ∈ vowels, IsFrontHarmonic x ↔ x = y ∨ x = ø := by decide

/-- The back harmonic vowels are /u/, /o/ and /ɒ/. -/
theorem isBackHarmonic_iff :
    ∀ x ∈ vowels, IsBackHarmonic x ↔ x = u ∨ x = o ∨ x = turnedScriptA := by
  decide

/-! ### The harmony systems -/

/-- Palatal harmony spreads the backness of the last harmonic stem vowel rightward to the
suffix vowels unspecified for it, consonants and the neutral vowels being off the tier. -/
def palatalHarmony : System Segment :=
  System.mk' (feature := .back)
    (IsTarget := fun s ↦ s.HasValue .syllabic true ∧ s .back = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true ∨ IsNeutral s)
    (direction := .rightward)

/-- Rounding harmony spreads the rounding of the last stem vowel to the suffix vowels
unspecified for it, with no transparent vowels; it matters only for front stems, since a
back stem takes the back alternant of a three-way suffix. -/
def labialHarmony : System Segment :=
  System.mk' (feature := .round)
    (IsTarget := fun s ↦ s.HasValue .syllabic true ∧ s .round = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true)
    (direction := .rightward)

end Hungarian

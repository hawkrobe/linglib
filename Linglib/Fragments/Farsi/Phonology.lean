import Linglib.Data.PHOIBLE.Inventories.Persian
import Linglib.Phonology.Segmental.Defs

/-!
# Persian (Farsi) phonology

The Persian segment inventory. `phonemeInventory` passes through the canonical
PHOIBLE doculect; the named segments are feature bundles for the six-vowel
system /i e æ u o ɑ/ and the consonants of the /hutʃɑ/ hiatus paradigm of
`Studies/Storme2026.lean`.

## References

* [M.-R. Majidi and E. Ternes, *Persian (Farsi)*][majidi-ternes-1991]
* [S. Moran and D. McCloy, *PHOIBLE 2.0*][moran-mccloy-2019]
* [B. Hayes, *Introductory Phonology*][hayes-2009]
* [K. Ariyaee and P. Jurgec, *Variable hiatus in Persian is affected by
  suffix length*][ariyaee-jurgec-2021]
-/

open Phonology

namespace Farsi.Phonology

/-- Canonical Persian phoneme inventory: first PHOIBLE inventory for ISO
`pes` (the Stanford Phonology Archive doculect). -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.Persian.pes

/-! ### Vowels

The six-vowel system of modern Persian ([majidi-ternes-1991]). -/

/-- /i/ — high front unrounded vowel. -/
def i : Segment := .vowel .high .front

/-- /e/ — mid front unrounded vowel. -/
def e : Segment := .vowel .mid .front

/-- /æ/ — low front unrounded vowel. -/
def ae : Segment := .vowel .low .front

/-- /u/ — high back rounded vowel. -/
def u : Segment := (Segment.vowel .high .back).setFeature .round true

/-- /o/ — mid back rounded vowel. -/
def o : Segment := (Segment.vowel .mid .back).setFeature .round true

/-- /ɑ/ — low back vowel, variably rounded [ɑ ~ ɒ]. -/
def aa : Segment := .vowel .low .back

/-! ### Consonants -/

/-- /h/ — voiceless glottal fricative. -/
def h : Segment := Segment.ofSpecs
  [(.syllabic, false), (.consonantal, false), (.sonorant, false),
   (.continuant, true), (.voice, false), (.spreadGlottis, true)]

/-- /tʃ/ — voiceless postalveolar affricate. -/
def ch : Segment := Segment.ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false),
   (.continuant, false), (.delayedRelease, true), (.voice, false),
   (.coronal, true), (.anterior, false), (.strident, true)]

/-- /m/ — bilabial nasal. -/
def m : Segment := Segment.ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, true),
   (.nasal, true), (.voice, true), (.labial, true)]

/-- /n/ — alveolar nasal. -/
def n : Segment := Segment.ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, true),
   (.nasal, true), (.voice, true), (.coronal, true), (.anterior, true)]

/-- /ʔ/ — glottal stop, the epenthetic hiatus-breaker. -/
def glottal : Segment := Segment.ofSpecs
  [(.syllabic, false), (.consonantal, false), (.sonorant, false),
   (.continuant, false), (.voice, false), (.constrGlottis, true)]

/-! ### Consistency with the substrate and with PHOIBLE -/

/-- The six vowels are pairwise distinct feature bundles. -/
example : ([i, e, ae, u, o, aa] : List Segment).Pairwise (· ≠ ·) := by decide

/-- All six vowels are vowels; none of the consonants is. -/
example : (∀ v ∈ ([i, e, ae, u, o, aa] : List Segment), v.IsVowel) ∧
    ∀ c ∈ ([h, ch, m, n, glottal] : List Segment), ¬c.IsVowel := by decide

/-- Every segment named here has its glyph in the canonical PHOIBLE doculect
(whose SPA transcription writes /æ/ as `a̟` and /tʃ/ as `t̠ʃ`). -/
example : ∀ g ∈ ["i", "e", "a̟", "u", "o", "ɑ", "h", "t̠ʃ", "m", "n", "ʔ"],
    g ∈ phonemeInventory.phonemes.map (·.glyph) := by decide

end Farsi.Phonology

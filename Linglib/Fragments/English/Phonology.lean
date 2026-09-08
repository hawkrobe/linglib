import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.LocalRewrite
import Linglib.Data.PHOIBLE.Inventories.English

/-!
# English phonology

Segments of English in [hayes-2009]'s feature system, each a partial specification so that
a bundle doubles as the natural class it names, two of the book's English rules as local
rewrite rules, and the PHOIBLE inventory ([moran-mccloy-2019]) the fragment is checked
against.

## References

* [hayes-2009]
* [moran-mccloy-2019]
-/

open Phonology
open Subregular.LocalRewrite

namespace English.Phonology

/-! ### Segments -/

/-- /p/: voiceless bilabial stop -/
def p : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.labial, true)]

/-- /t/: voiceless alveolar stop -/
def t : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.coronal, true), (Feature.anterior, true)]

/-- /k/: voiceless velar stop -/
def k : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.dorsal, true)]

/-- /b/: voiced bilabial stop -/
def b : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, true), (Feature.labial, true)]

/-- /d/: voiced alveolar stop -/
def d : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true)]

/-- /g/: voiced velar stop -/
def g : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, true), (Feature.dorsal, true)]

/-- /dʒ/: voiced postalveolar affricate -/
def dezh : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false), (Feature.delayedRelease, true),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, false),
   (Feature.distributed, true), (Feature.strident, true)]

/-- /m/: bilabial nasal -/
def m : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.continuant, false), (Feature.nasal, true),
   (Feature.voice, true), (Feature.labial, true)]

/-- /n/: alveolar nasal -/
def n : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.continuant, false), (Feature.nasal, true),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true)]

/-- /ŋ/: velar nasal -/
def ŋ : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.continuant, false), (Feature.nasal, true),
   (Feature.voice, true), (Feature.dorsal, true)]

/-- /f/: voiceless labiodental fricative -/
def f : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, true),
   (Feature.voice, false), (Feature.labial, true), (Feature.labiodental, true),
   (Feature.strident, true)]

/-- /v/: voiced labiodental fricative -/
def v : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, true),
   (Feature.voice, true), (Feature.labial, true), (Feature.labiodental, true),
   (Feature.strident, true)]

/-- /s/: voiceless alveolar fricative -/
def s : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, true),
   (Feature.voice, false), (Feature.coronal, true), (Feature.anterior, true),
   (Feature.strident, true)]

/-- /θ/: voiceless dental fricative -/
def θ : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, true),
   (Feature.voice, false), (Feature.coronal, true), (Feature.anterior, true),
   (Feature.distributed, true), (Feature.strident, false)]

/-- /ʃ/: voiceless postalveolar fricative -/
def esh : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, true),
   (Feature.voice, false), (Feature.coronal, true), (Feature.anterior, false),
   (Feature.distributed, true), (Feature.strident, true)]

/-- /l/: alveolar lateral -/
def l : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.approximant, true), (Feature.lateral, true),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true)]

/-- /w/: labial-velar glide -/
def w : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.labial, true), (Feature.dorsal, true),
   (Feature.high, true)]

/-- /r/: alveolar approximant -/
def r : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true)]

/-- /æ/: low front unrounded vowel -/
def æ : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.high, false), (Feature.low, true), (Feature.front, true)]

/-- /ɪ/: high front lax vowel -/
def laxI : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.low, false), (Feature.front, true),
   (Feature.tense, false)]

/-- /i/: high front tense vowel -/
def tenseI : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.low, false), (Feature.front, true),
   (Feature.tense, true)]

/-- /ʌ/: mid back lax unrounded vowel -/
def wedge : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.high, false), (Feature.low, false), (Feature.back, true), (Feature.front, false),
   (Feature.round, false), (Feature.tense, false)]

/-- /o/: mid back tense rounded vowel -/
def o : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.high, false), (Feature.low, false), (Feature.back, true), (Feature.front, false),
   (Feature.labial, true), (Feature.round, true), (Feature.tense, true)]

/-- /ə/: mid central vowel (schwa) -/
def schwa : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true)]

/-! ### Rules -/

/-- Preglottalization: a voiceless stop is glottalized word-finally,
`[−cont, −voice] → [+c.g.] / __ ]word`. -/
def preglottalization : Rule where
  name := "Preglottalization"
  target := Segment.ofSpecs [(Feature.continuant, false), (Feature.voice, false)]
  effect := .changeFeatures (Segment.ofSpecs [(Feature.constrGlottis, true)])
  rightContext := [.wordBoundary]

/-- Postnasal /t/ deletion: a voiceless coronal stop deletes between a nasal and a vowel,
`[−cont, +cor, +ant, −voice] → ∅ / [+nasal] __ [+syll]`. -/
def postnasalDeletion : Rule where
  name := "Postnasal /t/ Deletion"
  target := Segment.ofSpecs
    [(Feature.continuant, false), (Feature.coronal, true),
     (Feature.anterior, true), (Feature.voice, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(Feature.nasal, true)])]
  rightContext := [.seg (Segment.ofSpecs [(Feature.syllabic, true)])]

/-! ### The PHOIBLE inventory -/

/-- The PHOIBLE inventory of Standard English (inventory 160, the SPA doculect); the other
English doculects are in `Data.PHOIBLE.Inventories.English`. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.English.eng

end English.Phonology

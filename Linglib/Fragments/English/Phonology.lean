import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.RuleBased.Defs

/-!
# English Phonological Inventory

Concrete English segments and language-specific phonological rules,
defined using the SPE formalism from `Phonology.RuleBased.Defs`.

## Segments

Core inventory for demo alternations: /p t k b d m n ŋ s w r æ ɪ ə/.

## Rules

1. **Preglottalization** (Hayes p.125): `[-cont, -voice] → [+c.g.] / __]word`
2. **Postnasal /t/ Deletion** (Hayes p.133): `[-cont, +cor, +ant, -voice] → ∅ / [+nasal] __ [+syll]`

@cite{hayes-2009}
-/

namespace Fragments.English.Phonology

open Phonology
open Phonology.RuleBased

-- ============================================================================
-- § 1: Segment Inventory
-- ============================================================================

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

/-- /m/: bilabial nasal -/
def m : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.nasal, true),
   (Feature.voice, true), (Feature.labial, true)]

/-- /n/: alveolar nasal -/
def n : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.nasal, true),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true)]

/-- /ŋ/: velar nasal -/
def ŋ : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.nasal, true),
   (Feature.voice, true), (Feature.dorsal, true)]

/-- /s/: voiceless alveolar fricative -/
def s : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, true),
   (Feature.voice, false), (Feature.coronal, true), (Feature.anterior, true),
   (Feature.strident, true)]

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

/-- /ə/: mid central vowel (schwa) -/
def schwa : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true)]

-- ============================================================================
-- § 2: Rules
-- ============================================================================

/-- Preglottalization (Hayes p.125):
    `[-cont, -voice] → [+c.g.] / __]word`

    Voiceless stops become glottalized word-finally. -/
def preglottalization : PhonRule where
  name := "Preglottalization"
  target := Segment.ofSpecs [(Feature.continuant, false), (Feature.voice, false)]
  effect := .changeFeatures (Segment.ofSpecs [(Feature.constrGlottis, true)])
  rightContext := [.wordBoundary]

/-- Postnasal /t/ Deletion (Hayes p.133):
    `[-cont, +cor, +ant, -voice] → ∅ / [+nasal] __ [+syll]`

    Voiceless coronal stops delete between a nasal and a vowel. -/
def postnasalDeletion : PhonRule where
  name := "Postnasal /t/ Deletion"
  target := Segment.ofSpecs
    [(Feature.continuant, false), (Feature.coronal, true),
     (Feature.anterior, true), (Feature.voice, false)]
  effect := .delete
  leftContext := [.seg (Segment.ofSpecs [(Feature.nasal, true)])]
  rightContext := [.seg (Segment.ofSpecs [(Feature.syllabic, true)])]

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- /t/ is a voiceless stop: [-cont, -voice]. -/
theorem t_is_voiceless_stop :
    t.hasValue Feature.continuant false = true ∧
    t.hasValue Feature.voice false = true :=
  ⟨by native_decide, by native_decide⟩

/-- /n/ is a nasal: [+nasal, +son]. -/
theorem n_is_nasal :
    n.hasValue Feature.nasal true = true ∧
    n.hasValue Feature.sonorant true = true :=
  ⟨by native_decide, by native_decide⟩

/-- /æ/ is a vowel: [+syll, +son]. -/
theorem æ_is_vowel :
    æ.hasValue Feature.syllabic true = true ∧
    æ.hasValue Feature.sonorant true = true :=
  ⟨by native_decide, by native_decide⟩

/-- /k/ is a voiceless velar stop: [-cont, -voice, +dor]. -/
theorem k_is_voiceless_velar_stop :
    k.hasValue Feature.continuant false = true ∧
    k.hasValue Feature.voice false = true ∧
    k.hasValue Feature.dorsal true = true :=
  ⟨by native_decide, by native_decide, by native_decide⟩

end Fragments.English.Phonology

import Linglib.Phonology.Features
import Linglib.Phonology.Subregular.LocalRewrite
import Linglib.Data.PHOIBLE.Inventories.English

/-!
# English Phonological Inventory

Concrete English segments and language-specific phonological rules,
defined using the SPE formalism from `Subregular.LocalRewrite`.

## Segments

Core inventory for demo alternations: /p t k b d m n ŋ s w r æ ɪ ə/.

## Rules

1. **Preglottalization** (Hayes p.125): `[-cont, -voice] → [+c.g.] / __]word`
2. **Postnasal /t/ Deletion** (Hayes p.133): `[-cont, +cor, +ant, -voice] → ∅ / [+nasal] __ [+syll]`

[hayes-2009]
-/

open Phonology
open Subregular.LocalRewrite

namespace English.Phonology

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
def preglottalization : Rule where
  name := "Preglottalization"
  target := Segment.ofSpecs [(Feature.continuant, false), (Feature.voice, false)]
  effect := .changeFeatures (Segment.ofSpecs [(Feature.constrGlottis, true)])
  rightContext := [.wordBoundary]

/-- Postnasal /t/ Deletion (Hayes p.133):
    `[-cont, +cor, +ant, -voice] → ∅ / [+nasal] __ [+syll]`

    Voiceless coronal stops delete between a nasal and a vowel. -/
def postnasalDeletion : Rule where
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
    t.HasValue Feature.continuant false = true ∧
    t.HasValue Feature.voice false = true :=
  ⟨by decide, by decide⟩

/-- /n/ is a nasal: [+nasal, +son]. -/
theorem n_is_nasal :
    n.HasValue Feature.nasal true = true ∧
    n.HasValue Feature.sonorant true = true :=
  ⟨by decide, by decide⟩

/-- /æ/ is a vowel: [+syll, +son]. -/
theorem æ_is_vowel :
    æ.HasValue Feature.syllabic true = true ∧
    æ.HasValue Feature.sonorant true = true :=
  ⟨by decide, by decide⟩

/-- /k/ is a voiceless velar stop: [-cont, -voice, +dor]. -/
theorem k_is_voiceless_velar_stop :
    k.HasValue Feature.continuant false = true ∧
    k.HasValue Feature.voice false = true ∧
    k.HasValue Feature.dorsal true = true :=
  ⟨by decide, by decide, by decide⟩

-- ============================================================================
-- § 4: PHOIBLE-canonical inventory
-- ============================================================================

/-- Canonical English phoneme inventory: PHOIBLE InvID 160 ("stan1293"
    Standard English, source SPA). PHOIBLE 2.0 has 5 English doculects;
    this picks SPA as the canonical Fragment-layer choice. Other
    inventories accessible via `Data.PHOIBLE.Inventories.English`
    directly.

    Co-located with the Hayes-2009 SPE-style segments above (which are a
    different, theory-laden representation): SPE features are inferential
    primitives in `Phonology/Features.lean`; PHOIBLE
    inventory is the consensus-data alternative. -/
def phonemeInventory : Data.PHOIBLE.Inventory :=
  Data.PHOIBLE.Inventories.English.eng

end English.Phonology

import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.RuleBased.Defs

/-!
# Korean Phonological Inventory

Korean segments and the stop nasalization rule, using the SPE formalism
from `Phonology.RuleBased.Defs`.

## Segments

Core inventory for the nasalization demo: /p t k m n a u l/.
Korean stops are specified as [-del.rel.] (non-affricate), which is the
target feature for the nasalization rule.

## Rules

1. **Stop Nasalization** (Hayes p.132): `[-del.rel.] → [+nasal, +voice, +son] / __ [+nasal]`

@cite{hayes-2009}
-/

namespace Fragments.Korean.Phonology

open Phonology
open Phonology.RuleBased

-- ============================================================================
-- § 1: Segment Inventory
-- ============================================================================

/-- /p/: voiceless bilabial stop (non-affricate) -/
def p : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.delayedRelease, false),
   (Feature.labial, true)]

/-- /t/: voiceless alveolar stop (non-affricate) -/
def t : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.delayedRelease, false),
   (Feature.coronal, true), (Feature.anterior, true)]

/-- /k/: voiceless velar stop (non-affricate) -/
def k : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.delayedRelease, false),
   (Feature.dorsal, true)]

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

/-- /a/: low vowel -/
def a : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true)]

/-- /u/: high back rounded vowel -/
def u : Segment := Segment.ofSpecs
  [(Feature.syllabic, true), (Feature.consonantal, false),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.dorsal, true),
   (Feature.high, true), (Feature.low, false), (Feature.back, true),
   (Feature.round, true)]

/-- /l/: alveolar lateral -/
def l : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.continuant, true),
   (Feature.voice, true), (Feature.coronal, true), (Feature.anterior, true),
   (Feature.lateral, true)]

-- ============================================================================
-- § 2: Rules
-- ============================================================================

/-- Stop Nasalization (Hayes p.132):
    `[-del.rel.] → [+nasal, +voice, +son] / __ [+nasal]`

    Non-affricate stops become nasalized before nasals. -/
def stopNasalization : PhonRule where
  name := "Korean Stop Nasalization"
  target := Segment.ofSpecs [(Feature.delayedRelease, false)]
  effect := .changeFeatures (Segment.ofSpecs
    [(Feature.nasal, true), (Feature.voice, true), (Feature.sonorant, true)])
  rightContext := [.seg (Segment.ofSpecs [(Feature.nasal, true)])]

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- Korean stops have [-del.rel.], matching the nasalization target. -/
theorem p_matches_nasalization_target :
    p.hasValue Feature.delayedRelease false = true := by native_decide

theorem t_matches_nasalization_target :
    t.hasValue Feature.delayedRelease false = true := by native_decide

theorem k_matches_nasalization_target :
    k.hasValue Feature.delayedRelease false = true := by native_decide

/-- Vowels and nasals lack [-del.rel.], so they don't trigger nasalization. -/
theorem a_not_nasalization_target :
    a.specified Feature.delayedRelease = false := by native_decide

theorem m_not_nasalization_target :
    m.specified Feature.delayedRelease = false := by native_decide

end Fragments.Korean.Phonology
